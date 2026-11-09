# Regression: queued complete frames precede a reader's published terminal.
import Base
import ../../../proof/FrameQueue.bend as Q
law false_terminal_overtakes_complete_frame:
  {Q.select(Q.Queue{[Q.Frame{0n, []}], Q.Ended{}, Some{Q.Eof{}}, False{}}) ==
    Q.Terminal{Q.Eof{}, Q.Queue{[Q.Frame{0n, []}], Q.Ended{}, None{}, False{}}} : Q.Selection}
def false_terminal_overtakes_complete_frame():
  {==}
