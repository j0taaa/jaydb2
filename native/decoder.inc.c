/* Lowering of the pinned trusted Codec boundary. No field constructor outside
 * drecipe exists in this machine. Parser/control metadata is separate
 * from decoded values. The original Bend decoder remains the legacy branch. */
#include "abi_accounted.h"
static volatile struct jaydb_native_accounted_progress jaydb_decoder_progress;
#if JAYDB_ACCOUNTED_CODEC
#include "decoder_memory.h"
_Static_assert(sizeof(Term)==sizeof(struct jaydb_word192),"recipe carrier");
static struct jaydb_decoder_memory *jaydb_decoder_memory;
static bool jaydb_accounted_enabled(void){return jaydb_active && jaydb_active->accounted;}
static void jaydb_decoder_cleanup(void) {
  while(jaydb_decoder_memory)jaydb_decoder_release_one(&jaydb_decoder_memory);
}
static void *dalloc(u64 bytes) {
  void *out=0;
  uint32_t error=jaydb_decoder_acquire(&jaydb_decoder_memory,bytes,&out);
  if(error)jaydb_abort(error,0);
  return out;
}
struct dorigin { struct jaydb_field_wire wire;u64 quantity; };
struct dframe {
  struct dframe *parent;
  struct dorigin origin;
  __uint128_t outer_pending;
  u64 kind,left,last_name_at,last_name_bytes;
  Term reverse,name;
  bool name_live;
};
#define DFRAME_SLOTS ((4096-sizeof(struct jaydb_decoder_memory)-4*sizeof(void *))/sizeof(struct dframe))
struct dchunk {
  struct dchunk *previous,*next;
  u64 used;
  struct dframe frame[DFRAME_SLOTS];
};
_Static_assert(DFRAME_SLOTS>0,"frame fits page");
_Static_assert(sizeof(struct dchunk)+sizeof(struct jaydb_decoder_memory)<=4096,"minimum frame chunk");
struct jaydb_decoder_ids {
  u64 VAbsent,VBool,VInt,VText,VListEmpty,VList,VRecordEmpty,VRecord,Field;
};
struct dctx {
  const struct jaydb_decoder_ids *ids;
  Env e;
  unsigned char *wire;
  u64 size,limit,cursor,decode_id;
  struct dchunk *chunk;
  struct dframe *top;
  void *critical_stack;
  struct jaydb_decoder_memory *stack_owner;
  u64 critical_bytes;
  Term text;bool text_live,value_live;
};
static struct dframe *dpush(struct dctx *c,const struct dorigin *o,u64 kind,u64 n,__uint128_t pending) {
  if(!c->chunk)c->chunk=dalloc(sizeof *c->chunk);
  if(c->chunk->used==DFRAME_SLOTS) {
    if(!c->chunk->next) {
      struct dchunk *next=dalloc(sizeof *next);next->previous=c->chunk;c->chunk->next=next;
    }
    c->chunk=c->chunk->next;
  }
  struct dframe *f=&c->chunk->frame[c->chunk->used++];
  f->parent=c->top;f->origin=*o;f->kind=kind;f->left=n;f->outer_pending=pending;
  f->name_live=false;f->last_name_at=0;f->last_name_bytes=0;c->top=f;return f;
}
static void dpop(struct dctx *c) {
  c->top=c->top->parent;
  if(!--c->chunk->used && c->chunk->previous)c->chunk=c->chunk->previous;
}
static struct jayacct_u128 dwords(__uint128_t n) {
  return (struct jayacct_u128){(u64)n,(u64)(n>>64)};
}
/* Raw components, not an already formed TermCtr. Existing children are sealed
 * before the final barrier; all actual required arena leaves are ensured
 * before the logical free-list/bump claim. No byte/arity/depth quota. */
static Term drecipe(struct dctx *c,const struct dorigin *origin,u64 operation,u64 cid,
                  u64 site,u64 count,const struct jaydb_word192 *components) {
  struct jaydb_guard *g=jaydb_active;
  struct jaydb_native_accounted_result *report=g->accounted_result;
  jaydb_decoder_progress.phase=JAYDB_DECODE_FIELD;
  struct jaydb_word192 header;
  struct jaydb_word192 *destinations[3];
  /* The fixed wire schema's largest node is VRegistro (three components).
   * This is not a bound on source constructors, handled by generic emission. */
  if(count>3)jaydb_abort(JAYDB_INVARIANT,0);
  u64 location=0,claim_value=0;u64 *claim=0;
  if(operation==JAYDB_RECIPE_CTR) {
    u32 cls=cls_fit(count);u64 words=1ull<<cls;
    location=jaydb_free[cls];
    if(location){claim=&jaydb_free[cls];claim_value=(u64)(*jaydb_heap_cell(c->e.mem,location));}
    else {
      location=jaydb_heap_next;
      if(words>jaydb_heap_words-location)jaydb_abort(JAYDB_SYSTEM,0);
      jaydb_arena_ensure(location,words);claim=&jaydb_heap_next;claim_value=location+words;
    }
    for(u64 i=0;i<count;++i)destinations[i]=(void *)jaydb_heap_cell(c->e.mem,location+i);
  }
  if(!c->critical_stack) {
    c->critical_bytes=jaydb_field_recipe_stack_v3();
    uint32_t error=jaydb_decoder_acquire_backing(&jaydb_decoder_memory,c->stack_owner,
      c->critical_bytes,&c->critical_stack);
    if(error)jaydb_abort(error,0);
  }
  __uint128_t deadline=g->stage_deadline_wide[g->stage];
  struct jaydb_field_recipe recipe={.operation=operation,.constructor_id=cid,.site_id=site,
    .location=location,.quantity=origin->quantity,.wire=origin->wire,
    .scope=g->accounted->scope,.ceiling=g->accounted->ceiling,.deadline=dwords(deadline),
    .components=components,.destinations=destinations,.count=count,.header=&header,
    .claim=claim,.claim_value=claim_value,
    .completed_count=&report->field_completed,.claim_count=&report->logical_claims};
  report->decode_id=c->decode_id;report->constructor_id=cid;report->site_id=site;
  ++report->field_calls;
  uint64_t status=jaydb_field_recipe_v3(&recipe,c->critical_stack,c->critical_bytes,&report->field);
  if(status!=JAYDB_FIELD_CONSTRUCTED || report->field.release_error) {
    if(status==JAYDB_FIELD_TIME)jaydb_abort(JAYDB_TIME,JAYDB_FIELD_REFUSAL_CODE);
    /* Only the authentic complete scope peak in field supplies a memory
     * witness. Runtime status stays private; local MEMORY cannot impersonate it. */
    jaydb_abort(JAYDB_RUNTIME,JAYDB_FIELD_REFUSAL_CODE);
  }
  Term result;memcpy(&result,&header,sizeof result);
  jaydb_decoder_progress.phase=JAYDB_DECODE_PARSE;return result;
}
static Term dpak(struct dctx *c,const struct dorigin *o,u64 cid,u64 payload,u64 site) {
  struct jaydb_word192 raw={.payload=payload};
  return drecipe(c,o,JAYDB_RECIPE_PAK,cid,site,1,&raw);
}
static Term dword(struct dctx *c,const struct dorigin *o,u64 payload,u64 site) {
  /* This is raw parser metadata, not a Term/scalar constructed before hold. */
  struct jaydb_word192 raw={.payload=payload};
  return drecipe(c,o,JAYDB_RECIPE_WORD,0,site,1,&raw);
}
static Term dnode(struct dctx *c,const struct dorigin *o,u64 cid,u64 n,Term a,Term b,Term d,u64 site) {
  /* Only children ALREADY constructed by their own recipe enter this path. */
  Term children[3]={a,b,d};struct jaydb_word192 raw[3];
  for(u64 i=0;i<n;++i) {
    Term child=cid_hot(cid)?rfc_seal(c->e,children[i]):children[i];
    memcpy(&raw[i],&child,sizeof child);
  }
  return drecipe(c,o,JAYDB_RECIPE_CTR,cid,site,n,raw);
}
static u64 dtake(struct dctx *c,Term x,u64 n,Term *fields) {
  if(term_tag(x)==TAG_PAK){fields[0]=term_loc(x);return 0;}
  return ctr_take(c->e,x,n,fields);
}
static Term dreverse(struct dctx *c,const struct dorigin *o,Term text) {
  Term result=dpak(c,o,CID_SNil,0,21);
  while(term_aux(text)==CID_SCon) {
    Term fields[2];spare_free(c->e,1,dtake(c,text,2,fields));
    result=dnode(c,o,CID_SCon,2,fields[0],result,0,22);text=fields[1];
  }
  term_sink(c->e,text);return result;
}
/* 0=valid opened, 1=Entrada, 2=Limite. Only variable-length headers run
 * Codec.concluir_palavra's pending-minimum guard. Primitive tags emit directly;
 * Inteiro consumes its eight bytes and emits without this guard. In particular
 * a missing sibling must not prevent that integer's constructions or mask a
 * later variable-header overflow. Equality is allowed. */
static u64 dopen(struct dctx *c,__uint128_t pending,bool name,struct dorigin *o,u64 *tag) {
  if(c->cursor==c->size)return 1;
  u64 pos=c->cursor++,t=c->wire[pos],n=0,header=1;
  jaydb_decoder_progress.cursor=c->cursor;
  *tag=t;
  if(t>6 || (name && t!=4))return 1;
  if(t>=3) {
    if(c->size-c->cursor<8)return 1;
    if(t>=4){header=9;for(u64 i=0;i<8;++i) {
      n=(n<<8)|c->wire[c->cursor++];jaydb_decoder_progress.cursor=c->cursor;
    }}
    else n=8;
  }
  if(t>=4) {
    __uint128_t own=(__uint128_t)n*(t==6?11u:1u);
    if(pending>~(__uint128_t)0-own || own+pending>c->limit-pos-header)return 2;
    if(own+pending>c->size-pos-header)return 1;
  }
  if(name && (!n || n>64))return 1;
  *o=(struct dorigin){.wire={c->wire,c->size,c->limit,pos,name,dwords(pending)},.quantity=n};
  return 0;
}
static bool dutf(struct dctx *c,u64 end,u32 *cp) {
  jaydb_decoder_progress.phase=JAYDB_DECODE_UTF8;
  jaydb_decoder_progress.scalar_start=c->cursor;
  jaydb_decoder_progress.utf8_consumed=0;
  jaydb_decoder_progress.utf8_value=0;
  jaydb_decoder_progress.utf8_needed=0;
  if(c->cursor==end)return false;
  u32 b=c->wire[c->cursor++],n,min,value;
  jaydb_decoder_progress.cursor=c->cursor;
  jaydb_decoder_progress.utf8_consumed=1;
  jaydb_decoder_progress.utf8_value=b;
  if(b<128){*cp=b;return true;}
  if(b>=194 && b<=223){n=1;min=128;value=b-192;}
  else if(b>=224 && b<=239){n=2;min=2048;value=b-224;}
  else if(b>=240 && b<=244){n=3;min=65536;value=b-240;}
  else return false;
  jaydb_decoder_progress.utf8_value=value;
  jaydb_decoder_progress.utf8_needed=n;
  while(n--) {
    if(c->cursor==end)return false;
    b=c->wire[c->cursor++];jaydb_decoder_progress.cursor=c->cursor;
    jaydb_decoder_progress.utf8_consumed=c->cursor-jaydb_decoder_progress.scalar_start;
    if(b<128 || b>191)return false;value=value*64+b-128;
    jaydb_decoder_progress.utf8_value=value;jaydb_decoder_progress.utf8_needed=n;
  }
  if(value<min || value>1114111 || (value>=55296 && value<=57343))return false;
  *cp=value;return true;
}
static bool dname_byte(unsigned char b,bool first) {
  return (b>='a' && b<='z') || (b>='A' && b<='Z') || b=='_'
      || (!first && b>='0' && b<='9');
}
static bool dname_order(struct dctx *c,struct dframe *f,u64 at,u64 bytes) {
  if(!f->last_name_bytes)return true;
  u64 old=f->last_name_at,n=bytes<f->last_name_bytes?bytes:f->last_name_bytes;
  for(u64 i=0;i<n;++i) {
    if(c->wire[old+i]!=c->wire[at+i])return c->wire[old+i]<c->wire[at+i];
  }
  return f->last_name_bytes<bytes;
}
/* Called only from the generated, checked Codec entry with its ACTUAL bs.
 * No Native.read or private request.input/framing assumptions occur here. */
static void jaydb_codec_accounted(Env e,Term bs,u64 high,u64 low,Term *out,const struct jaydb_decoder_ids *ids) {
  struct jaydb_decoder_memory *checkpoint=jaydb_decoder_memory;
  struct jaydb_native_accounted_result *report=jaydb_active->accounted_result;
  struct dctx c={.ids=ids,.e=e,.limit=(high<<32)|(u32)low,.decode_id=++report->decoder_calls};
  jaydb_decoder_progress=(struct jaydb_native_accounted_progress){.abi=1,
    .phase=JAYDB_DECODE_COUNT,.decode_id=c.decode_id,.stage=jaydb_active->stage,
    .sampled_ns=jaydb_decoder_progress.sampled_ns};
  u64 outcome=1;Term value=0;
  for(Term scan=bs;term_aux(scan)==CID_Con;) {
    if(c.size==UINT64_MAX)jaydb_abort(JAYDB_SYSTEM,0);
    ++c.size;jaydb_decoder_progress.wire_size=c.size;
    scan=e.mem[term_peek(e.mem,scan)+1];
    if(term_aux(scan)!=CID_Con && term_aux(scan)!=CID_Nil)jaydb_abort(JAYDB_RUNTIME,0);
  }
  if(c.size>c.limit){outcome=2;goto done;}
  if(!c.size)goto done;
  if(c.size>SIZE_MAX-15-sizeof(struct jaydb_decoder_memory))jaydb_abort(JAYDB_SYSTEM,0);
  u64 owner_at=(c.size+15)&~UINT64_C(15);
  c.wire=dalloc(owner_at+sizeof(struct jaydb_decoder_memory));
  c.stack_owner=(void *)(c.wire+owner_at);
  jaydb_decoder_progress.phase=JAYDB_DECODE_COPY;
  { Term scan=bs;
    for(u64 i=0;i<c.size;++i) {
      u64 at=term_peek(e.mem,scan);Term byte=e.mem[at];
      if(byte>255)goto done;
      c.wire[i]=(unsigned char)byte;jaydb_decoder_progress.wire_copied=i+1;
      scan=e.mem[at+1];
    }
  }
  jaydb_decoder_progress.phase=JAYDB_DECODE_PARSE;
  for(;;) {
    struct dorigin origin;u64 tag;
    __uint128_t pending=c.top?c.top->outer_pending+(__uint128_t)(c.top->left-1)*(c.top->kind==6?11:1):0;
    if(c.top && c.top->kind==6) {
      struct dframe *f=c.top;struct dorigin name_origin;u64 name_tag;
      outcome=dopen(&c,pending+1,true,&name_origin,&name_tag);if(outcome)goto done;
      u64 at=c.cursor,bytes=name_origin.quantity,end=at+bytes;
      Term text=dpak(&c,&name_origin,CID_SNil,0,10);c.text=text;c.text_live=true;bool valid=true;u64 chars=0;
      while(c.cursor<end) {
        u32 cp;if(!dutf(&c,end,&cp))goto input;
        Term character=dword(&c,&name_origin,cp,11);
        text=dnode(&c,&name_origin,CID_SCon,2,character,text,0,12);c.text=text;
        if(cp>127 || !dname_byte((unsigned char)cp,chars==0))valid=false;
        ++chars;
      }
      text=dreverse(&c,&name_origin,text);c.text=text;
      if(!valid || !dname_order(&c,f,at,bytes))goto input;
      f->name=text;f->name_live=true;c.text_live=false;f->last_name_at=at;f->last_name_bytes=bytes;
    }
    outcome=dopen(&c,pending,false,&origin,&tag);if(outcome)goto done;
    if(tag<=2)value=dpak(&c,&origin,tag==0?c.ids->VAbsent:c.ids->VBool,tag==2,1);
    else if(tag==3) {
      u64 n=0;for(u64 i=0;i<8;++i) {
        n=(n<<8)|c.wire[c.cursor++];jaydb_decoder_progress.cursor=c.cursor;
      }
      Term high=dword(&c,&origin,(u32)(n>>32),6),low=dword(&c,&origin,(u32)n,7);
      value=dnode(&c,&origin,c.ids->VInt,2,high,low,0,2);
    } else if(tag==4) {
      u64 end=c.cursor+origin.quantity;
      Term text=dpak(&c,&origin,CID_SNil,0,10);c.text=text;c.text_live=true;
      while(c.cursor<end) {
        u32 cp;if(!dutf(&c,end,&cp))goto input;
        Term character=dword(&c,&origin,cp,11);
        text=dnode(&c,&origin,CID_SCon,2,character,text,0,12);c.text=text;
      }
      text=dreverse(&c,&origin,text);c.text=text;
      value=dnode(&c,&origin,c.ids->VText,1,text,0,0,3);c.text_live=false;
    } else if(!origin.quantity)value=dpak(&c,&origin,tag==5?c.ids->VListEmpty:c.ids->VRecordEmpty,0,4);
    else {
      struct dframe *f=dpush(&c,&origin,tag,origin.quantity,pending);
      f->reverse=dpak(&c,&origin,CID_Nil,0,5);continue;
    }
    for(;;) {
      c.value_live=true;
      if(!c.top) {
        if(c.cursor!=c.size)goto input;
        outcome=0;goto done;
      }
      struct dframe *f=c.top;
      Term item=value;
      if(f->kind==6){item=dnode(&c,&f->origin,c.ids->Field,2,f->name,value,0,30);f->name_live=false;}
      f->reverse=dnode(&c,&f->origin,CID_Con,2,item,f->reverse,0,31);c.value_live=false;
      if(--f->left)break;
      Term xs=f->reverse;
      value=dpak(&c,&f->origin,f->kind==5?c.ids->VListEmpty:c.ids->VRecordEmpty,0,32);
      while(term_aux(xs)==CID_Con) {
        Term pair[2];spare_free(e,1,dtake(&c,xs,2,pair));xs=pair[1];
        if(f->kind==5)value=dnode(&c,&f->origin,c.ids->VList,2,pair[0],value,0,33);
        else {
          Term field[2];spare_free(e,1,dtake(&c,pair[0],2,field));
          value=dnode(&c,&f->origin,c.ids->VRecord,3,field[0],field[1],value,34);
        }
      }
      term_sink(e,xs);dpop(&c);
    }
  }
input:outcome=1;
done:
  jaydb_decoder_progress.phase=outcome?JAYDB_DECODE_REJECTED:JAYDB_DECODE_DONE;
  if(outcome) {
    if(c.text_live)term_sink(e,c.text);
    if(c.value_live)term_sink(e,value);
    for(struct dframe *f=c.top;f;f=f->parent) {
      term_sink(e,f->reverse);if(f->name_live)term_sink(e,f->name);
    }
  }
  term_sink(e,bs);
  out[0]=outcome;out[1]=outcome?0:value;
  ++report->decoder_completed;
  while(jaydb_decoder_memory!=checkpoint)jaydb_decoder_release_one(&jaydb_decoder_memory);
}
#else
static bool jaydb_accounted_enabled(void){return false;}
static void jaydb_decoder_cleanup(void){}
#endif
