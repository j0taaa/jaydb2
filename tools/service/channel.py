"""Private counted receive/propose/complete/deliver path.

The caller supplies a fully initialized instance and its retained C root.
This is not a replacement initialization profile or an automatic opt-in for
the experimental CLI. Real incomplete observations continue to refuse entry.
"""
from __future__ import annotations

from .completion import RequestCompletion
from .controller import deliver
from .frames import error_frame


class CountedChannel:
    def __init__(self,database,root,counter,receiver,*,instrument_deadline_ns):
        if type(instrument_deadline_ns) is not int or instrument_deadline_ns<=0:
            raise ValueError('An exact instrument cleanup epoch is required')
        if receiver.counter is not counter:
            raise ValueError('Receiving and completion must use the same inherited counter')
        if root.state!=database.state:
            raise ValueError('The C root must retain the initialized published state')
        previous=getattr(database,'_published_root',None)
        if previous is not None and previous is not root:
            raise ValueError('The instance already belongs to another C root')
        self.database,self.root,self.counter,self.receiver=database,root,counter,receiver
        self.instrument_deadline_ns=instrument_deadline_ns
        self.last_frame=None
        self.last_completion=None
        self.ended=False

    def once(self,input_fd=0,output_fd=1):
        if self.ended:
            raise RuntimeError('The channel has already ended')
        try:
            return self._once(input_fd,output_fd)
        except BaseException:
            # An unusable/instrumented channel must not consume a second
            # request after an interrupted first byte, completion or delivery.
            self.ended=True
            raise

    def _once(self,input_fd,output_fd):
        db=self.database
        received=self.receiver.receive(input_fd,duration_ns=db.limits['enquadramento'],
            instrument_deadline_ns=self.instrument_deadline_ns,
            message_limit=db.limits['mensagem'],memory_ceiling=db.limits['memoria'])
        self.last_frame=received
        if received is None:
            self.ended=True
            return False # EOF between calls; no completion or response
        if received.status not in (None,'entrada','limite','falha'):
            raise ValueError('Receiving produced a status outside its stage')
        if received.status is not None and not received.close_channel:
            # A resource/error discovered after the last byte does not lose
            # synchronization. Closure follows the original reception extent,
            # independently of the selected response status.
            if (received.status not in ('limite','falha') or not received.framed
                    or len(received.body)>db.limits['mensagem']):
                raise ValueError('An incomplete failed frame must close the channel')
        completion=RequestCompletion(self.root,self.counter,received.start.scope,db.limits['memoria'])
        self.last_completion=completion
        if received.status is None:
            db.bind_request_completion(completion,
                instrument_deadline_ns=self.instrument_deadline_ns)
            response=db.request(received.body,framing_deadline=received.start.deadline_ns)
        else:
            # Header/body reception failed before any program operation. There
            # is no native request binding to consume, and no publication.
            response=completion.finish(error_frame(received.status),state=None,
                deadline_ns=received.start.deadline_ns,
                instrument_deadline_ns=self.instrument_deadline_ns)
        # No error mapper surrounds completion or delivery. The C root remains
        # authoritative if return/release/channel operations fail after store.
        if not completion.completed or response!=completion.response:
            raise RuntimeError('Delivery requires the durable completed response')
        self.ended=received.close_channel
        deliver(output_fd,response)
        return not self.ended

    def serve(self,input_fd=0,output_fd=1):
        while self.once(input_fd,output_fd):
            pass
