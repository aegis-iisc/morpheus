
module MenhirBasics = struct
  
  exception Error
  
  type token = 
    | UNION
    | UINST
    | TYPE
    | TRUE
    | SUBSETEQ
    | SUBSET
    | STRCONST of (
# 63 "specParser.mly"
       (string)
# 17 "specParser.ml"
  )
    | STEXC
    | STATE
    | STAR
    | SEMICOLON
    | RPAREN
    | RELATION
    | REF
    | RCURLY
    | RBRACE
    | PURE
    | PRIMITIVE
    | PRIME
    | PLUS
    | PIPE
    | OF
    | NUMEQ
    | NOT
    | MINUS
    | LPAREN
    | LESSTHAN
    | LCURLY
    | LBRACE
    | LAMBDA
    | INT of (
# 62 "specParser.mly"
       (int)
# 45 "specParser.ml"
  )
    | IMPL
    | IFF
    | ID of (
# 61 "specParser.mly"
        (string)
# 52 "specParser.ml"
  )
    | GREATERTHAN
    | FORMULA
    | FALSE
    | EXISTS
    | EXC
    | EQUALOP
    | EOL
    | EOF
    | DOT
    | DISJ
    | CROSSPRD
    | CONJ
    | COMMA
    | COLON
    | CHARCONST of (
# 64 "specParser.mly"
       (string)
# 71 "specParser.ml"
  )
    | ASSUME
    | ARROW
    | ARMINUS
    | ANGRIGHT
    | ANGLEFT
    | ALL
  
end

include MenhirBasics

let _eRR =
  MenhirBasics.Error

type _menhir_env = {
  _menhir_lexer: Lexing.lexbuf -> token;
  _menhir_lexbuf: Lexing.lexbuf;
  _menhir_token: token;
  mutable _menhir_error: bool
}

and _menhir_state = 
  | MenhirState258
  | MenhirState256
  | MenhirState254
  | MenhirState252
  | MenhirState250
  | MenhirState247
  | MenhirState242
  | MenhirState238
  | MenhirState234
  | MenhirState232
  | MenhirState223
  | MenhirState216
  | MenhirState214
  | MenhirState210
  | MenhirState206
  | MenhirState195
  | MenhirState193
  | MenhirState191
  | MenhirState188
  | MenhirState184
  | MenhirState182
  | MenhirState180
  | MenhirState178
  | MenhirState176
  | MenhirState171
  | MenhirState170
  | MenhirState168
  | MenhirState167
  | MenhirState164
  | MenhirState160
  | MenhirState157
  | MenhirState136
  | MenhirState135
  | MenhirState133
  | MenhirState131
  | MenhirState129
  | MenhirState128
  | MenhirState126
  | MenhirState116
  | MenhirState115
  | MenhirState110
  | MenhirState108
  | MenhirState104
  | MenhirState101
  | MenhirState94
  | MenhirState93
  | MenhirState91
  | MenhirState86
  | MenhirState84
  | MenhirState78
  | MenhirState76
  | MenhirState74
  | MenhirState72
  | MenhirState68
  | MenhirState62
  | MenhirState59
  | MenhirState54
  | MenhirState51
  | MenhirState50
  | MenhirState49
  | MenhirState47
  | MenhirState37
  | MenhirState35
  | MenhirState33
  | MenhirState25
  | MenhirState23
  | MenhirState20
  | MenhirState17
  | MenhirState16
  | MenhirState12
  | MenhirState7
  | MenhirState5
  | MenhirState3
  | MenhirState0

# 1 "specParser.mly"
  
open SpecLang
open RelLang
open Printf
module TypeSpec = SpecLang.RelSpec.TypeSpec
module RefTy = SpecLang.RefinementType
module Formula = SpecLang.RelSpec.Formula
let defaultCons = SpecLang.Tycon.default
let symbase = "sp_"
let count = ref 0
let genVar = fun _ -> 
  let id = symbase ^ (string_of_int (!count)) in 
  let () = count := !count + 1
    in
      Var.fromString id 
let ($) (f,arg) = f arg
let  empty = fun _ -> Vector.new0 ()
let print msg = let () = Printf.printf "%s" msg in ()


# 191 "specParser.ml"

let rec _menhir_goto_decsandtys : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_decsandtys -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState258 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv991 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv989 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_predspec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 130 "specParser.mly"
    (
		 match d with 
		  RelSpec.T {typedefs;preds;reldecs; primdecs; typespecs} -> 
                    RelSpec.T {typedefs=typedefs;preds= p :: preds;reldecs = reldecs; primdecs=primdecs;
                      typespecs = typespecs}

		)
# 216 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv990)) : 'freshtv992)
    | MenhirState256 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv995 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv993 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_primdec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 112 "specParser.mly"
                (match d with 
                  RelSpec.T ({typedefs;preds;reldecs; primdecs; typespecs}) -> 
                    RelSpec.T {
                              typedefs=typedefs;
                              preds = preds;
		    		                  primdecs = p :: primdecs; 
                              reldecs=reldecs; 
                              typespecs = typespecs}
                )
# 241 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv994)) : 'freshtv996)
    | MenhirState254 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv999 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv997 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (r : 'tv_reldec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 102 "specParser.mly"
                  (
                    match d with 
                    RelSpec.T ({typedefs;preds;reldecs; primdecs; typespecs}) -> 
                    RelSpec.T {typedefs=typedefs;
                              preds = preds;
		    		                  reldecs = r ::reldecs; 
                              primdecs = primdecs;
                            typespecs = typespecs}
                          )
# 266 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv998)) : 'freshtv1000)
    | MenhirState252 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1003 * _menhir_state * 'tv_typedef)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1001 * _menhir_state * 'tv_typedef)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (td : 'tv_typedef)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 89 "specParser.mly"
                  (
                    match d with 
                          RelSpec.T ({typedefs;preds;reldecs; primdecs; typespecs}) ->    
                              RelSpec.T {
                              typedefs = td :: typedefs;
                              preds = preds;
                              reldecs = reldecs; 
                              primdecs = primdecs;
                              typespecs = typespecs}
                  )
# 292 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1002)) : 'freshtv1004)
    | MenhirState250 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1007 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv1005 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let (_menhir_stack, _menhir_s, (t : 'tv_typespec)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_decsandtys = 
# 123 "specParser.mly"
                (
                  match d with
                 RelSpec.T {typedefs;preds;reldecs; primdecs;typespecs} -> 
                    RelSpec.T {typedefs=typedefs;preds= preds;reldecs = reldecs; primdecs=primdecs;
                      typespecs = t :: typespecs}
                )
# 314 "specParser.ml"
         in
        _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1006)) : 'freshtv1008)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1021) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_decsandtys) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1019) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let ((d : 'tv_decsandtys) : 'tv_decsandtys) = _v in
        ((let _v : 'tv_spec = 
# 84 "specParser.mly"
                   (
                  d)
# 330 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1017) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_spec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1015 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EOF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1011 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1009 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (s : 'tv_spec)) = _menhir_stack in
            let _2 = () in
            let _v : (
# 77 "specParser.mly"
       (SpecLang.RelSpec.t)
# 352 "specParser.ml"
            ) = 
# 80 "specParser.mly"
               (s)
# 356 "specParser.ml"
             in
            _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv1010)) : 'freshtv1012)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv1013 * _menhir_state * 'tv_spec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv1014)) : 'freshtv1016)) : 'freshtv1018)) : 'freshtv1020)) : 'freshtv1022)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typespec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_typespec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv987 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv983 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | FORMULA ->
            _menhir_run240 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | ID _v ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack) MenhirState250 _v
        | LPAREN ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | PRIMITIVE ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | RELATION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | TYPE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | EOF ->
            _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack) MenhirState250
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState250) : 'freshtv984)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv985 * _menhir_state * 'tv_typespec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv986)) : 'freshtv988)

and _menhir_goto_vartyseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState126 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv977 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv973 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ARROW ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv967 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_vartyatom = 
# 294 "specParser.mly"
                                  (
                match vas with
                        [x] -> x 
                        | _ -> (genVar (), RefTy.Sigma vas)
                  )
# 440 "specParser.ml"
                 in
                _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv968)
            | COMMA | LCURLY | RPAREN | SEMICOLON ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv969 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (vas : 'tv_vartyseq)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_reftyatom = 
# 286 "specParser.mly"
                                        (RefTy.Sigma vas)
# 452 "specParser.ml"
                 in
                _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv970)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv971 * _menhir_state) * _menhir_state * 'tv_vartyseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv972)) : 'freshtv974)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv975 * _menhir_state) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv976)) : 'freshtv978)
    | MenhirState232 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv981 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv979 * _menhir_state * 'tv_varty)) * _menhir_state * 'tv_vartyseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_varty)), _, (vts : 'tv_vartyseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_vartyseq = 
# 301 "specParser.mly"
                                       (vt :: vts)
# 479 "specParser.ml"
         in
        _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv980)) : 'freshtv982)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatchseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatchseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv957 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 493 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv955 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 501 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 508 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _5 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_reldec = 
# 170 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = p;
                mapp = patmseq})
# 518 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv956)) : 'freshtv958)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv961 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv959 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((pms : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatchseq = 
# 190 "specParser.mly"
                                               (pm :: pms)
# 535 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv960)) : 'freshtv962)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv965 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 543 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_patmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv963 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 551 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((patmseq : 'tv_patmatchseq) : 'tv_patmatchseq) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 558 "specParser.ml"
        ))) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_reldec = 
# 166 "specParser.mly"
          (StructuralRelation.T {id=RelId.fromString i;
                params = empty ();
                mapp = patmseq})
# 566 "specParser.ml"
         in
        _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv964)) : 'freshtv966)
    | _ ->
        _menhir_fail ()

and _menhir_goto_funparams : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_funparams -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv949 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv945 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv943 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (ps : 'tv_funparams)) = _menhir_stack in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_ratom = 
# 242 "specParser.mly"
                                               (MultiR (ie, ps))
# 594 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv944)) : 'freshtv946)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv947 * _menhir_state * 'tv_instexpr)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv948)) : 'freshtv950)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv953 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv951 * _menhir_state * 'tv_funparam)) * _menhir_state * 'tv_funparams) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (p : 'tv_funparam)), _, (ps : 'tv_funparams)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_funparams = 
# 252 "specParser.mly"
                                 (p::ps)
# 614 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv952)) : 'freshtv954)
    | _ ->
        _menhir_fail ()

and _menhir_goto_reftyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reftyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv941) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_reftyatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv939) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((rta : 'tv_reftyatom) : 'tv_reftyatom) = _v in
    ((let _v : 'tv_refty = 
# 281 "specParser.mly"
                      ( rta)
# 633 "specParser.ml"
     in
    _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv940)) : 'freshtv942)

and _menhir_reduce22 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _v : 'tv_decsandtys = 
# 137 "specParser.mly"
                (RelSpec.T {
                    typedefs=[];
  			            preds = Vector.new0 ();
  			            reldecs = [];
                    primdecs = Vector.new0 ();
                    typespecs = []})
# 647 "specParser.ml"
     in
    _menhir_goto_decsandtys _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_refty : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_refty -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState216 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv899 * _menhir_state * 'tv_vartyatom)) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv897 * _menhir_state * 'tv_vartyatom)) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vrta : 'tv_vartyatom)), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_refty = 
# 282 "specParser.mly"
                                      ( RefTy.Arrow (((fst (vrta)) , (snd vrta)), rt))
# 665 "specParser.ml"
         in
        _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv898)) : 'freshtv900)
    | MenhirState214 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv905 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 673 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 677 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv901 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 687 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 691 "specParser.ml"
            ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState223 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState223
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState223) : 'freshtv902)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv903 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 729 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 733 "specParser.ml"
            ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv904)) : 'freshtv906)
    | MenhirState234 | MenhirState128 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv925 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 742 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv923 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 748 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 753 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_varty = 
# 304 "specParser.mly"
  (((Var.fromString i), rt))
# 759 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv921) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_varty) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv919 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv913 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv911) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState232 in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 784 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv907 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 795 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState234 _v
                    | LBRACE ->
                        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState234
                    | LCURLY ->
                        _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState234
                    | LPAREN ->
                        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState234
                    | PRIME ->
                        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState234
                    | REF ->
                        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState234
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState234) : 'freshtv908)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : 'freshtv909 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 823 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv910)) : 'freshtv912)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState232) : 'freshtv914)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv915 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (vt : 'tv_varty)) = _menhir_stack in
            let _v : 'tv_vartyseq = 
# 300 "specParser.mly"
                    ([vt])
# 838 "specParser.ml"
             in
            _menhir_goto_vartyseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv916)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv917 * _menhir_state * 'tv_varty) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv918)) : 'freshtv920)) : 'freshtv922)) : 'freshtv924)) : 'freshtv926)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv929 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 853 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv927 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 859 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((((_menhir_stack, _menhir_s), _, (ps : 'tv_paramseq)), (i : (
# 61 "specParser.mly"
        (string)
# 864 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _5 = () in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typespec = 
# 275 "specParser.mly"
                                                         (
                                  TypeSpec.T {isAssume = false;
                                name = Var.fromString i;
                                params = Vector.fromList ps; 
                                refty = rt})
# 876 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv928)) : 'freshtv930)
    | MenhirState238 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv933 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 884 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv931 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 890 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 895 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_typespec = 
# 271 "specParser.mly"
                               (      TypeSpec.T {isAssume = false;
                                       name = (Var.fromString i);
                                       params = empty ();
                                       refty = rt})
# 904 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv932)) : 'freshtv934)
    | MenhirState247 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv937 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 912 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv935 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 918 "specParser.ml"
        ))) * _menhir_state * 'tv_refty) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 923 "specParser.ml"
        ))), _, (rt : 'tv_refty)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typespec = 
# 266 "specParser.mly"
                                      (
                                          TypeSpec.T {isAssume = true;
                                              name = (Var.fromString i);
                                              params = empty ();
                                              refty = rt})
# 934 "specParser.ml"
         in
        _menhir_goto_typespec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv936)) : 'freshtv938)
    | _ ->
        _menhir_fail ()

and _menhir_run176 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState176 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState176
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState176

and _menhir_run178 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState178 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState178 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState178
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState178

and _menhir_run180 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState180
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState180 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState180
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState180
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState180
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState180

and _menhir_run182 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState182
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState182 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState182 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState182
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState182
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState182
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState182

and _menhir_run184 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState184
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState184 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState184
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState184
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState184
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState184

and _menhir_goto_rpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv895) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_rpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv893) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ra : 'tv_rpatom) : 'tv_rpatom) = _v in
    ((let _v : 'tv_patom = 
# 345 "specParser.mly"
                  (Predicate.Rel ra)
# 1063 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv894)) : 'freshtv896)

and _menhir_goto_primdef : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_primdef -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv879 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1075 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv877 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1083 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 1090 "specParser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_primdef = 
# 161 "specParser.mly"
                                    (PrimitiveRelation.Nary
                (Var.fromString i, p))
# 1098 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv878)) : 'freshtv880)
    | MenhirState101 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv891 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 1106 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdef) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv889 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 1114 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((p : 'tv_primdef) : 'tv_primdef) = _v in
        ((let ((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 1121 "specParser.ml"
        ))) = _menhir_stack in
        let _4 = () in
        let _2 = () in
        let _1 = () in
        let _v : 'tv_primdec = 
# 156 "specParser.mly"
                                                    (PrimitiveRelation.T
                    {id=RelId.fromString i; 
                    def=PrimitiveRelation.alphaRename p})
# 1131 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv887) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_primdec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv885 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv881 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run245 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | FORMULA ->
                _menhir_run240 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | ID _v ->
                _menhir_run237 _menhir_env (Obj.magic _menhir_stack) MenhirState256 _v
            | LPAREN ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | PRIMITIVE ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | RELATION ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | TYPE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | EOF ->
                _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack) MenhirState256
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState256) : 'freshtv882)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv883 * _menhir_state * 'tv_primdec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv884)) : 'freshtv886)) : 'freshtv888)) : 'freshtv890)) : 'freshtv892)
    | _ ->
        _menhir_fail ()

and _menhir_goto_patmatch : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patmatch -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv875 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv869 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
        | LPAREN ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState91
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91) : 'freshtv870)
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv871 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (pm : 'tv_patmatch)) = _menhir_stack in
        let _v : 'tv_patmatchseq = 
# 191 "specParser.mly"
                          ([pm])
# 1208 "specParser.ml"
         in
        _menhir_goto_patmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv872)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv873 * _menhir_state * 'tv_patmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv874)) : 'freshtv876)

and _menhir_run57 : _menhir_env -> ('ttv_tail * _menhir_state) * _menhir_state * 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv867 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
    ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
    let _3 = () in
    let _1 = () in
    let _v : 'tv_ratom = 
# 244 "specParser.mly"
                               (re)
# 1230 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv868)

and _menhir_goto_reldec : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_reldec -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv865 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv861 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ASSUME ->
            _menhir_run245 _menhir_env (Obj.magic _menhir_stack) MenhirState254
        | FORMULA ->
            _menhir_run240 _menhir_env (Obj.magic _menhir_stack) MenhirState254
        | ID _v ->
            _menhir_run237 _menhir_env (Obj.magic _menhir_stack) MenhirState254 _v
        | LPAREN ->
            _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState254
        | PRIMITIVE ->
            _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState254
        | RELATION ->
            _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState254
        | TYPE ->
            _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState254
        | EOF ->
            _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack) MenhirState254
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState254) : 'freshtv862)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv863 * _menhir_state * 'tv_reldec) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv864)) : 'freshtv866)

and _menhir_reduce29 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1279 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1285 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_funparam = 
# 254 "specParser.mly"
                (Var.fromString i)
# 1290 "specParser.ml"
     in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv859) = _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_funparam) = _v in
    ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv857 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv851 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv849) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState68 in
            let (_v : (
# 61 "specParser.mly"
        (string)
# 1315 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack)) : 'freshtv850)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState68) : 'freshtv852)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv853 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (p : 'tv_funparam)) = _menhir_stack in
        let _v : 'tv_funparams = 
# 251 "specParser.mly"
                       ([p])
# 1331 "specParser.ml"
         in
        _menhir_goto_funparams _menhir_env _menhir_stack _menhir_s _v) : 'freshtv854)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv855 * _menhir_state * 'tv_funparam) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv856)) : 'freshtv858)) : 'freshtv860)

and _menhir_goto_instexprs : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexprs -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState49 | MenhirState51 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv843 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1350 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv841 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1358 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1365 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_instexpr = 
# 223 "specParser.mly"
                              (RInst {
                sargs = empty (); targs = empty();
                args = Vector.fromList ies;
                rel = RelId.fromString i})
# 1373 "specParser.ml"
         in
        _menhir_goto_instexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv842)) : 'freshtv844)
    | MenhirState54 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv847 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_instexprs) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv845 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((ies : 'tv_instexprs) : 'tv_instexprs) = _v in
        ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_instexprs = 
# 229 "specParser.mly"
                                                    (ie :: ies)
# 1391 "specParser.ml"
         in
        _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv846)) : 'freshtv848)
    | _ ->
        _menhir_fail ()

and _menhir_goto_vartyatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_vartyatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv839 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARROW ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv835 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState216 _v
        | LBRACE ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | LCURLY ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | LPAREN ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | PRIME ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | REF ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState216
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState216) : 'freshtv836)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv837 * _menhir_state * 'tv_vartyatom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv838)) : 'freshtv840)

and _menhir_reduce73 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_basety -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (bt : 'tv_basety)) = _menhir_stack in
    let _v : 'tv_reftyatom = 
# 285 "specParser.mly"
                      ( bt)
# 1441 "specParser.ml"
     in
    _menhir_goto_reftyatom _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_tpatmatchseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tpatmatchseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv829 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1453 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_tpatmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv827 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 1461 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((cons : 'tv_tpatmatchseq) : 'tv_tpatmatchseq) = _v in
        ((let ((_menhir_stack, _menhir_s), (tn : (
# 61 "specParser.mly"
        (string)
# 1468 "specParser.ml"
        ))) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_typedef = 
# 146 "specParser.mly"
                (Algebraic.TD {
                    typename = Var.fromString tn;   
                    constructors = cons    
                    }
                )
# 1479 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv825) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_typedef) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv823 * _menhir_state * 'tv_typedef) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv819 * _menhir_state * 'tv_typedef) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run245 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | FORMULA ->
                _menhir_run240 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | ID _v ->
                _menhir_run237 _menhir_env (Obj.magic _menhir_stack) MenhirState252 _v
            | LPAREN ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | PRIMITIVE ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | RELATION ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | TYPE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | EOF ->
                _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack) MenhirState252
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState252) : 'freshtv820)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv821 * _menhir_state * 'tv_typedef) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv822)) : 'freshtv824)) : 'freshtv826)) : 'freshtv828)) : 'freshtv830)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv833 * _menhir_state * 'tv_tpatmatch)) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_tpatmatchseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv831 * _menhir_state * 'tv_tpatmatch)) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((tpms : 'tv_tpatmatchseq) : 'tv_tpatmatchseq) = _v in
        ((let (_menhir_stack, _menhir_s, (tpm : 'tv_tpatmatch)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tpatmatchseq = 
# 194 "specParser.mly"
                                                    (tpm :: tpms)
# 1538 "specParser.ml"
         in
        _menhir_goto_tpatmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv832)) : 'freshtv834)
    | _ ->
        _menhir_fail ()

and _menhir_goto_typenameseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_typenameseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    match _menhir_s with
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv813 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1552 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_typenameseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv811 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1560 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((tnseq : 'tv_typenameseq) : 'tv_typenameseq) = _v in
        ((let (_menhir_stack, _menhir_s, (typename : (
# 61 "specParser.mly"
        (string)
# 1567 "specParser.ml"
        ))) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_typenameseq = 
# 203 "specParser.mly"
                                                   (TyD.fromString (typename):: tnseq)
# 1573 "specParser.ml"
         in
        _menhir_goto_typenameseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv812)) : 'freshtv814)
    | MenhirState5 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv817 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1581 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_typenameseq) = _v in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv815 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1589 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        let (_ : _menhir_state) = _menhir_s in
        let ((typeargs : 'tv_typenameseq) : 'tv_typenameseq) = _v in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1596 "specParser.ml"
        ))) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tpatmatch = 
# 201 "specParser.mly"
                                        (Algebraic.Const {name=i;args=typeargs})
# 1602 "specParser.ml"
         in
        _menhir_goto_tpatmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv816)) : 'freshtv818)
    | _ ->
        _menhir_fail ()

and _menhir_goto_idseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_idseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv801 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1617 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv799 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1623 "specParser.ml"
        ))) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 1628 "specParser.ml"
        ))), _, (is : 'tv_idseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_idseq = 
# 218 "specParser.mly"
                            ((Var.fromString i)::is)
# 1634 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv800)) : 'freshtv802)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv809) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv805) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv803) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _, (is : 'tv_idseq)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_conargs = 
# 215 "specParser.mly"
                                 (Vector.fromList is)
# 1655 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv804)) : 'freshtv806)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv807) * _menhir_state * 'tv_idseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv808)) : 'freshtv810)
    | _ ->
        _menhir_fail ()

and _menhir_goto_pred : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_pred -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv713 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv711 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 339 "specParser.mly"
                                           (Predicate.Exists (binds, pr))
# 1683 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv712)) : 'freshtv714)
    | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv717 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv715 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 334 "specParser.mly"
                              (Predicate.If (pa,pr))
# 1696 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv716)) : 'freshtv718)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv721 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv719 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 335 "specParser.mly"
                             (Predicate.Iff (pa,pr))
# 1709 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv720)) : 'freshtv722)
    | MenhirState193 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv725 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv723 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 337 "specParser.mly"
                              (Predicate.Disj (pa,pr))
# 1722 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv724)) : 'freshtv726)
    | MenhirState195 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv729 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv727 * _menhir_state * 'tv_patom)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (pa : 'tv_patom)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_pred = 
# 336 "specParser.mly"
                              (Predicate.Conj (pa,pr))
# 1735 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv728)) : 'freshtv730)
    | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv733 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv731 * _menhir_state) * _menhir_state * 'tv_tybindseq)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), _, (binds : 'tv_tybindseq)), _, (pr : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_pred = 
# 338 "specParser.mly"
                                           (Predicate.Forall (binds, pr) )
# 1749 "specParser.ml"
         in
        _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv732)) : 'freshtv734)
    | MenhirState136 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv741 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv737 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv735 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (pr : 'tv_pred)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_patom = 
# 343 "specParser.mly"
                              (pr)
# 1770 "specParser.ml"
             in
            _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv736)) : 'freshtv738)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv739 * _menhir_state) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv740)) : 'freshtv742)
    | MenhirState133 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv749 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1785 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv745 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1795 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv743 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1802 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), _, (v : (
# 61 "specParser.mly"
        (string)
# 1807 "specParser.ml"
            ))), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _7 = () in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 321 "specParser.mly"
                                                       (RefinementType.Base ((Var.fromString v), 
                ty, pr))
# 1817 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv744)) : 'freshtv746)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((((('freshtv747 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1827 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv748)) : 'freshtv750)
    | MenhirState206 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv757 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv753 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv751 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)), _, (pr : 'tv_pred)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 319 "specParser.mly"
                                           (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, pr))
# 1851 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv752)) : 'freshtv754)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv755 * _menhir_state) * _menhir_state * 'tv_tyd)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv756)) : 'freshtv758)
    | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv771 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1866 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv767 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1876 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv763 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1886 "specParser.ml"
                ))) * _menhir_state * 'tv_pred)) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 1891 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (((('freshtv759 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1902 "specParser.ml"
                    ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1906 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState214 _v
                    | LBRACE ->
                        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState214
                    | LCURLY ->
                        _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState214
                    | LPAREN ->
                        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState214
                    | PRIME ->
                        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState214
                    | REF ->
                        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState214
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState214) : 'freshtv760)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (((('freshtv761 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1934 "specParser.ml"
                    ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1938 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv762)) : 'freshtv764)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv765 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1949 "specParser.ml"
                ))) * _menhir_state * 'tv_pred)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv766)) : 'freshtv768)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv769 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1960 "specParser.ml"
            ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv770)) : 'freshtv772)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((((('freshtv785 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1969 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1973 "specParser.ml"
        ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv781 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1983 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1987 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv779 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 1994 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 1998 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s, (ef : (
# 61 "specParser.mly"
        (string)
# 2003 "specParser.ml"
            ))), _, (pre : 'tv_pred)), (resvar : (
# 61 "specParser.mly"
        (string)
# 2007 "specParser.ml"
            ))), _, (resty : 'tv_refty)), _, (post : 'tv_pred)) = _menhir_stack in
            let _10 = () in
            let _8 = () in
            let _6 = () in
            let _4 = () in
            let _2 = () in
            let _v : 'tv_mty = 
# 324 "specParser.mly"
                                                                                         (RefTy.MArrow (Effect.fromString ef, pre, (resvar, resty), post))
# 2017 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv777) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv775) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_mty) = _v in
            ((let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv773) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let ((mtype : 'tv_mty) : 'tv_mty) = _v in
            ((let _v : 'tv_refty = 
# 283 "specParser.mly"
                  (mtype)
# 2034 "specParser.ml"
             in
            _menhir_goto_refty _menhir_env _menhir_stack _menhir_s _v) : 'freshtv774)) : 'freshtv776)) : 'freshtv778)) : 'freshtv780)) : 'freshtv782)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((((('freshtv783 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2044 "specParser.ml"
            ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 2048 "specParser.ml"
            ))) * _menhir_state * 'tv_refty)) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv784)) : 'freshtv786)
    | MenhirState242 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv797 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2057 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv795 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2063 "specParser.ml"
        ))) * _menhir_state * 'tv_pred) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 2068 "specParser.ml"
        ))), _, (p : 'tv_pred)) = _menhir_stack in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_predspec = 
# 154 "specParser.mly"
                                       (Formula.Form{name=Var.fromString i;pred = p})
# 2075 "specParser.ml"
         in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv793) = _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        let (_v : 'tv_predspec) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv791 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv787 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ASSUME ->
                _menhir_run245 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | FORMULA ->
                _menhir_run240 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | ID _v ->
                _menhir_run237 _menhir_env (Obj.magic _menhir_stack) MenhirState258 _v
            | LPAREN ->
                _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | PRIMITIVE ->
                _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | RELATION ->
                _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | TYPE ->
                _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | EOF ->
                _menhir_reduce22 _menhir_env (Obj.magic _menhir_stack) MenhirState258
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState258) : 'freshtv788)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv789 * _menhir_state * 'tv_predspec) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv790)) : 'freshtv792)) : 'freshtv794)) : 'freshtv796)) : 'freshtv798)
    | _ ->
        _menhir_fail ()

and _menhir_goto_rexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_rexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv641 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv639 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv640)) : 'freshtv642)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv645 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv643 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 233 "specParser.mly"
                                (U(ra,re))
# 2152 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv644)) : 'freshtv646)
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv649 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv647 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 235 "specParser.mly"
                               (ADD(ra,re))
# 2165 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv648)) : 'freshtv650)
    | MenhirState74 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv653 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv651 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 234 "specParser.mly"
                                (D(ra,re))
# 2178 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv652)) : 'freshtv654)
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv657 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv655 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 232 "specParser.mly"
                                   (X(ra,re))
# 2191 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv656)) : 'freshtv658)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv661 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv659 * _menhir_state * 'tv_ratom)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (ra : 'tv_ratom)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rexpr = 
# 236 "specParser.mly"
                                  (SUBS(ra,re))
# 2204 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv660)) : 'freshtv662)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv665 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv663 * _menhir_state) * 'tv_conpat))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (((_menhir_stack, _menhir_s), (cp : 'tv_conpat)), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _4 = () in
        let _3 = () in
        let _1 = () in
        let _v : 'tv_patmatch = 
# 207 "specParser.mly"
              (match cp with (c,vlop) -> (c, vlop, Expr re))
# 2219 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv664)) : 'freshtv666)
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv669 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2227 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv667 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2233 "specParser.ml"
        ))) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 2238 "specParser.ml"
        ))), _, (re : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_patmatch = 
# 208 "specParser.mly"
                                 ((Tycon.fromString i, None, Expr re))
# 2244 "specParser.ml"
         in
        _menhir_goto_patmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv668)) : 'freshtv670)
    | MenhirState101 | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv673 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv671 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (re : 'tv_rexpr)) = _menhir_stack in
        let _v : 'tv_primdef = 
# 160 "specParser.mly"
                   (PrimitiveRelation.Nullary re)
# 2256 "specParser.ml"
         in
        _menhir_goto_primdef _menhir_env _menhir_stack _menhir_s _v) : 'freshtv672)) : 'freshtv674)
    | MenhirState171 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv681 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGRIGHT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv677 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv675 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (re : 'tv_rexpr)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_rpatom = 
# 370 "specParser.mly"
                                   (Predicate.RelPredicate.Q (re))
# 2277 "specParser.ml"
             in
            _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv676)) : 'freshtv678)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv679 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv680)) : 'freshtv682)
    | MenhirState242 | MenhirState223 | MenhirState210 | MenhirState206 | MenhirState133 | MenhirState135 | MenhirState167 | MenhirState195 | MenhirState193 | MenhirState191 | MenhirState188 | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv685 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run178 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run176 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv683 * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv684)) : 'freshtv686)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv689 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv687 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 373 "specParser.mly"
                                      (Predicate.RelPredicate.SubEq(re1,re2))
# 2320 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv688)) : 'freshtv690)
    | MenhirState178 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv693 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv691 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 372 "specParser.mly"
                                    (Predicate.RelPredicate.Sub(re1,re2))
# 2333 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv692)) : 'freshtv694)
    | MenhirState180 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv697 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv695 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 374 "specParser.mly"
                                   (Predicate.RelPredicate.NEq(re1, re2) )
# 2346 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv696)) : 'freshtv698)
    | MenhirState182 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv701 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv699 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 375 "specParser.mly"
                                         (Predicate.RelPredicate.Grt(re1, re2))
# 2359 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv700)) : 'freshtv702)
    | MenhirState184 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv705 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv703 * _menhir_state * 'tv_rexpr)) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (re1 : 'tv_rexpr)), _, (re2 : 'tv_rexpr)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_rpatom = 
# 371 "specParser.mly"
                                     (Predicate.RelPredicate.Eq(re1,re2))
# 2372 "specParser.ml"
         in
        _menhir_goto_rpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv704)) : 'freshtv706)
    | MenhirState136 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv709 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            _menhir_run184 _menhir_env (Obj.magic _menhir_stack)
        | GREATERTHAN ->
            _menhir_run182 _menhir_env (Obj.magic _menhir_stack)
        | NUMEQ ->
            _menhir_run180 _menhir_env (Obj.magic _menhir_stack)
        | RPAREN ->
            _menhir_run57 _menhir_env (Obj.magic _menhir_stack)
        | SUBSET ->
            _menhir_run178 _menhir_env (Obj.magic _menhir_stack)
        | SUBSETEQ ->
            _menhir_run176 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv707 * _menhir_state) * _menhir_state * 'tv_rexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv708)) : 'freshtv710)
    | _ ->
        _menhir_fail ()

and _menhir_goto_instexpr : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_instexpr -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv607 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv603 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | LBRACE ->
                _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState54
            | LPAREN | RBRACE | STAR ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv601 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (ie : 'tv_instexpr)) = _menhir_stack in
                let _3 = () in
                let _1 = () in
                let _v : 'tv_instexprs = 
# 228 "specParser.mly"
                                      ([ie])
# 2430 "specParser.ml"
                 in
                _menhir_goto_instexprs _menhir_env _menhir_stack _menhir_s _v) : 'freshtv602)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54) : 'freshtv604)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv605 * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv606)) : 'freshtv608)
    | MenhirState242 | MenhirState210 | MenhirState223 | MenhirState206 | MenhirState133 | MenhirState135 | MenhirState136 | MenhirState167 | MenhirState170 | MenhirState195 | MenhirState193 | MenhirState191 | MenhirState188 | MenhirState184 | MenhirState182 | MenhirState180 | MenhirState178 | MenhirState176 | MenhirState171 | MenhirState101 | MenhirState104 | MenhirState84 | MenhirState33 | MenhirState35 | MenhirState78 | MenhirState76 | MenhirState74 | MenhirState72 | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv621 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv617 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ('freshtv615 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState62 in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 2463 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RPAREN ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv611 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2474 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv609 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2481 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, (ie : 'tv_instexpr)), _, (i : (
# 61 "specParser.mly"
        (string)
# 2486 "specParser.ml"
                    ))) = _menhir_stack in
                    let _4 = () in
                    let _2 = () in
                    let _v : 'tv_ratom = 
# 243 "specParser.mly"
                                       (R (ie, Var.fromString i))
# 2493 "specParser.ml"
                     in
                    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv610)) : 'freshtv612)
                | COMMA ->
                    _menhir_reduce29 _menhir_env (Obj.magic _menhir_stack)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : (('freshtv613 * _menhir_state * 'tv_instexpr)) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2505 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv614)) : 'freshtv616)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62) : 'freshtv618)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv619 * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv620)) : 'freshtv622)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((((('freshtv629 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2525 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv625 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2535 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv623 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2542 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (((((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 2547 "specParser.ml"
            ))), _, (p : 'tv_params)), _), _, (ie : 'tv_instexpr)) = _menhir_stack in
            let _8 = () in
            let _6 = () in
            let _5 = () in
            let _2 = () in
            let _1 = () in
            let _v : 'tv_reldec = 
# 179 "specParser.mly"
          (StructuralRelation.T{id=RelId.fromString i;
                params = p;
                mapp = [(defaultCons,None,
                  Star ie)]})
# 2560 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv624)) : 'freshtv626)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (((((('freshtv627 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 2570 "specParser.ml"
            )) * _menhir_state * 'tv_params)) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv628)) : 'freshtv630)
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv637 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2579 "specParser.ml"
        )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | STAR ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv633 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2589 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv631 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2596 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let ((((_menhir_stack, _menhir_s), (i : (
# 61 "specParser.mly"
        (string)
# 2601 "specParser.ml"
            ))), _), _, (ie : 'tv_instexpr)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_reldec = 
# 174 "specParser.mly"
          (StructuralRelation.T{id=RelId.fromString i;
                params = empty ();
                mapp = [(defaultCons,None,
                  Star ie)]})
# 2612 "specParser.ml"
             in
            _menhir_goto_reldec _menhir_env _menhir_stack _menhir_s _v) : 'freshtv632)) : 'freshtv634)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv635 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 2622 "specParser.ml"
            )) * _menhir_state) * _menhir_state * 'tv_instexpr) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv636)) : 'freshtv638)
    | _ ->
        _menhir_fail ()

and _menhir_reduce69 : _menhir_env -> 'ttv_tail * _menhir_state * 'tv_elem -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
    let _v : 'tv_ratom = 
# 246 "specParser.mly"
                (V (el))
# 2635 "specParser.ml"
     in
    _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_elemseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_elemseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv595 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv591 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv587 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv585 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _, (els : 'tv_elemseq)) = _menhir_stack in
                let _5 = () in
                let _4 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 241 "specParser.mly"
                                                (T(Vector.fromList els))
# 2669 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv586)) : 'freshtv588)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : ((('freshtv589 * _menhir_state)) * _menhir_state * 'tv_elemseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv590)) : 'freshtv592)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv593 * _menhir_state)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv594)) : 'freshtv596)
    | MenhirState47 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv599 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv597 * _menhir_state * 'tv_elem)) * _menhir_state * 'tv_elemseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (el : 'tv_elem)), _, (els : 'tv_elemseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_elemseq = 
# 257 "specParser.mly"
                                    (el::els)
# 2696 "specParser.ml"
         in
        _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv598)) : 'freshtv600)
    | _ ->
        _menhir_fail ()

and _menhir_fail : unit -> 'a =
  fun () ->
    Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
    assert false

and _menhir_goto_basety : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_basety -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState247 | MenhirState238 | MenhirState115 | MenhirState234 | MenhirState214 | MenhirState216 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv575 * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        (_menhir_reduce73 _menhir_env (Obj.magic _menhir_stack) : 'freshtv576)
    | MenhirState128 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv583 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2720 "specParser.ml"
        ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv579 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2730 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv577 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2737 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), _, (i : (
# 61 "specParser.mly"
        (string)
# 2742 "specParser.ml"
            ))), _, (bt : 'tv_basety)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_vartyatom = 
# 289 "specParser.mly"
  (
                  match bt with 
                     RefTy.Base (v,_,_) -> ((Var.fromString i),bt)
                       | _ -> raise (Failure "Impossible case of basety")
		)
# 2754 "specParser.ml"
             in
            _menhir_goto_vartyatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv578)) : 'freshtv580)
        | COMMA ->
            _menhir_reduce73 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv581 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2766 "specParser.ml"
            ))) * _menhir_state * 'tv_basety) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv582)) : 'freshtv584)
    | _ ->
        _menhir_fail ()

and _menhir_goto_tybindseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tybindseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv561 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv559 * _menhir_state * 'tv_vartybind)) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (vt : 'tv_vartybind)), _, (vts : 'tv_tybindseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_tybindseq = 
# 379 "specParser.mly"
                                            (vt :: vts)
# 2787 "specParser.ml"
         in
        _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv560)) : 'freshtv562)
    | MenhirState157 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv567 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv563 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState167 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState167
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState167) : 'freshtv564)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv565 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv566)) : 'freshtv568)
    | MenhirState168 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv573 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv569 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState170 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState170
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState170) : 'freshtv570)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv571 * _menhir_state) * _menhir_state * 'tv_tybindseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv572)) : 'freshtv574)
    | _ ->
        _menhir_fail ()

and _menhir_goto_tpatmatch : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tpatmatch -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv557 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | PIPE ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv551 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12) : 'freshtv552)
    | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv553 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (tpm : 'tv_tpatmatch)) = _menhir_stack in
        let _v : 'tv_tpatmatchseq = 
# 195 "specParser.mly"
                            ([tpm])
# 2910 "specParser.ml"
         in
        _menhir_goto_tpatmatchseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv554)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv555 * _menhir_state * 'tv_tpatmatch) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv556)) : 'freshtv558)

and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 2924 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | STAR ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv545 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2936 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState7 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState7) : 'freshtv546)
    | PIPE | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv547 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2952 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (typename : (
# 61 "specParser.mly"
        (string)
# 2957 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_typenameseq = 
# 204 "specParser.mly"
                            ([TyD.fromString (typename)])
# 2962 "specParser.ml"
         in
        _menhir_goto_typenameseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv548)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv549 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2972 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv550)

and _menhir_goto_params : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_params -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv535 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2986 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv533 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 2992 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 2997 "specParser.ml"
        ))), _, (p : 'tv_params)) = _menhir_stack in
        let _v : 'tv_params = 
# 185 "specParser.mly"
                       ((RelId.fromString i)::p)
# 3002 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv534)) : 'freshtv536)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv543 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 3010 "specParser.ml"
        )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv539 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 3020 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | EQUALOP ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (((('freshtv537 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 3030 "specParser.ml"
                )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
                let (_menhir_s : _menhir_state) = MenhirState20 in
                ((let _menhir_stack = (_menhir_stack, _menhir_s) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | ID _v ->
                    _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState86 _v
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState86) : 'freshtv538)
            | ID _v ->
                _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState20 _v
            | LPAREN ->
                _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState20
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState20) : 'freshtv540)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv541 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 3058 "specParser.ml"
            )) * _menhir_state * 'tv_params) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv542)) : 'freshtv544)
    | _ ->
        _menhir_fail ()

and _menhir_goto_conpat : _menhir_env -> 'ttv_tail -> 'tv_conpat -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_stack = (_menhir_stack, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : ('freshtv531 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv527 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv523 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState33 _v
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | LPAREN ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | TRUE ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState33
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState33) : 'freshtv524)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : (('freshtv525 * _menhir_state) * 'tv_conpat)) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv526)) : 'freshtv528)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv529 * _menhir_state) * 'tv_conpat) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv530)) : 'freshtv532)

and _menhir_run24 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 3119 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv517 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3131 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState25 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25) : 'freshtv518)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv519 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3147 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3152 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_idseq = 
# 217 "specParser.mly"
             ([Var.fromString i])
# 3157 "specParser.ml"
         in
        _menhir_goto_idseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv520)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv521 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3167 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv522)

and _menhir_goto_conargs : _menhir_env -> 'ttv_tail -> 'tv_conargs -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv515 * (
# 61 "specParser.mly"
        (string)
# 3178 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let (_v : 'tv_conargs) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv513 * (
# 61 "specParser.mly"
        (string)
# 3185 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let ((co : 'tv_conargs) : 'tv_conargs) = _v in
    ((let (_menhir_stack, (i : (
# 61 "specParser.mly"
        (string)
# 3191 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_conpat = 
# 212 "specParser.mly"
                          ((Tycon.fromString i, Some co))
# 3196 "specParser.ml"
     in
    _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv514)) : 'freshtv516)

and _menhir_goto_paramseq : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_paramseq -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv497 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3209 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv495 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3215 "specParser.ml"
        ))) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3220 "specParser.ml"
        ))), _, (pseq : 'tv_paramseq)) = _menhir_stack in
        let _2 = () in
        let _v : 'tv_paramseq = 
# 188 "specParser.mly"
                                  ((RelId.fromString i)::pseq)
# 3226 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv496)) : 'freshtv498)
    | MenhirState108 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv511 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv507 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv503 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 3247 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | COLON ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv499 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 3258 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let _tok = _menhir_env._menhir_token in
                    match _tok with
                    | ID _v ->
                        _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState115 _v
                    | LBRACE ->
                        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | LCURLY ->
                        _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | LPAREN ->
                        _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | PRIME ->
                        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | REF ->
                        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState115
                    | _ ->
                        assert (not _menhir_env._menhir_error);
                        _menhir_env._menhir_error <- true;
                        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState115) : 'freshtv500)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv501 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 3286 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv502)) : 'freshtv504)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv505 * _menhir_state) * _menhir_state * 'tv_paramseq)) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv506)) : 'freshtv508)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv509 * _menhir_state) * _menhir_state * 'tv_paramseq) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv510)) : 'freshtv512)
    | _ ->
        _menhir_fail ()

and _menhir_reduce24 : _menhir_env -> 'ttv_tail * _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s) = _menhir_stack in
    let t = () in
    let _v : 'tv_elem = 
# 260 "specParser.mly"
              (Bool(true))
# 3314 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_goto_patom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_patom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState242 | MenhirState210 | MenhirState223 | MenhirState206 | MenhirState133 | MenhirState136 | MenhirState167 | MenhirState195 | MenhirState193 | MenhirState191 | MenhirState188 | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv489 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | CONJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv477 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState195 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState195
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState195) : 'freshtv478)
        | DISJ ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv479 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState193 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState193
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState193) : 'freshtv480)
        | IFF ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv481 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState191 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState191
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState191) : 'freshtv482)
        | IMPL ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv483 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState188 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState188
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState188) : 'freshtv484)
        | RCURLY | RPAREN | SEMICOLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv485 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (pa : 'tv_patom)) = _menhir_stack in
            let _v : 'tv_pred = 
# 333 "specParser.mly"
                 (pa)
# 3463 "specParser.ml"
             in
            _menhir_goto_pred _menhir_env _menhir_stack _menhir_s _v) : 'freshtv486)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv487 * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv488)) : 'freshtv490)
    | MenhirState135 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv493 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv491 * _menhir_state) * _menhir_state * 'tv_patom) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (pa : 'tv_patom)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 342 "specParser.mly"
                     (Predicate.Not pa)
# 3483 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv492)) : 'freshtv494)
    | _ ->
        _menhir_fail ()

and _menhir_goto_ratom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_ratom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv475 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
    ((assert (not _menhir_env._menhir_error);
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ARMINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv461 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState78
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78) : 'freshtv462)
    | CROSSPRD ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv463 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState76
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76) : 'freshtv464)
    | MINUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv465 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState74
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74) : 'freshtv466)
    | PLUS ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv467 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState72
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72) : 'freshtv468)
    | UNION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv469 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState59
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59) : 'freshtv470)
    | ANGRIGHT | CONJ | DISJ | EQUALOP | GREATERTHAN | IFF | IMPL | NUMEQ | PIPE | RCURLY | RPAREN | SEMICOLON | SUBSET | SUBSETEQ ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv471 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ra : 'tv_ratom)) = _menhir_stack in
        let _v : 'tv_rexpr = 
# 237 "specParser.mly"
                 (ra)
# 3614 "specParser.ml"
         in
        _menhir_goto_rexpr _menhir_env _menhir_stack _menhir_s _v) : 'freshtv472)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv473 * _menhir_state * 'tv_ratom) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv474)) : 'freshtv476)

and _menhir_run41 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 3628 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce26 _menhir_env (Obj.magic _menhir_stack)

and _menhir_goto_bpatom : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_bpatom -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv459) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : 'tv_bpatom) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv457) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ba : 'tv_bpatom) : 'tv_bpatom) = _v in
    ((let _v : 'tv_patom = 
# 344 "specParser.mly"
                  (Predicate.Base ba)
# 3648 "specParser.ml"
     in
    _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv458)) : 'freshtv460)

and _menhir_reduce26 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3655 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3661 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_elem = 
# 262 "specParser.mly"
            (Var(Var.fromString i))
# 3666 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v

and _menhir_reduce34 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3673 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 3679 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_instexpr = 
# 220 "specParser.mly"
                (RInst { sargs = empty (); 
                targs = empty(); args = empty (); 
                rel = RelId.fromString i})
# 3686 "specParser.ml"
     in
    _menhir_goto_instexpr _menhir_env _menhir_stack _menhir_s _v

and _menhir_run50 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState50 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState50

and _menhir_goto_elem : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_elem -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState47 | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv445 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COMMA ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv439 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState47
            | ID _v ->
                _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState47 _v
            | TRUE ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState47
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState47) : 'freshtv440)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv441 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, (el : 'tv_elem)) = _menhir_stack in
            let _v : 'tv_elemseq = 
# 256 "specParser.mly"
                  ([el])
# 3738 "specParser.ml"
             in
            _menhir_goto_elemseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv442)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv443 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv444)) : 'freshtv446)
    | MenhirState242 | MenhirState210 | MenhirState223 | MenhirState206 | MenhirState133 | MenhirState135 | MenhirState167 | MenhirState170 | MenhirState195 | MenhirState193 | MenhirState191 | MenhirState188 | MenhirState184 | MenhirState182 | MenhirState180 | MenhirState178 | MenhirState176 | MenhirState171 | MenhirState101 | MenhirState104 | MenhirState84 | MenhirState33 | MenhirState78 | MenhirState76 | MenhirState74 | MenhirState72 | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv447 * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        (_menhir_reduce69 _menhir_env (Obj.magic _menhir_stack) : 'freshtv448)
    | MenhirState136 | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv455 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv451 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv449 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (el : 'tv_elem)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_ratom = 
# 245 "specParser.mly"
                              (T[el])
# 3770 "specParser.ml"
             in
            _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv450)) : 'freshtv452)
        | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | SUBSET | SUBSETEQ | UNION ->
            _menhir_reduce69 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv453 * _menhir_state) * _menhir_state * 'tv_elem) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv454)) : 'freshtv456)
    | _ ->
        _menhir_fail ()

and _menhir_run158 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv435 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 3797 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv431 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3808 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run123 _menhir_env (Obj.magic _menhir_stack) MenhirState160 _v
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState160
            | PRIME ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState160
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState160
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState160) : 'freshtv432)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv433 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3832 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv434)) : 'freshtv436)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv437 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv438)

and _menhir_run123 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 3847 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run124 _menhir_env (Obj.magic _menhir_stack) _v
    | COMMA | LCURLY | PIPE | RCURLY | RPAREN | SEMICOLON ->
        _menhir_reduce102 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv429 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3865 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv430)

and _menhir_goto_tyd : _menhir_env -> 'ttv_tail -> _menhir_state -> 'tv_tyd -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    match _menhir_s with
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv389 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv387 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _, (t : 'tv_tyd)) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_tyd = 
# 310 "specParser.mly"
             (TyD.makeTRef t )
# 3884 "specParser.ml"
         in
        _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv388)) : 'freshtv390)
    | MenhirState131 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv395 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3892 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv391 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3902 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState133
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133) : 'freshtv392)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv393 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 3940 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv394)) : 'freshtv396)
    | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv413 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3949 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv409 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3959 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv407 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 3966 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (((_menhir_stack, _menhir_s), (v : (
# 61 "specParser.mly"
        (string)
# 3971 "specParser.ml"
            ))), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _5 = () in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_vartybind = 
# 382 "specParser.mly"
   ((v, ty))
# 3979 "specParser.ml"
             in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv405) = _menhir_stack in
            let (_menhir_s : _menhir_state) = _menhir_s in
            let (_v : 'tv_vartybind) = _v in
            ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv403 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
            ((assert (not _menhir_env._menhir_error);
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | COMMA ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv397 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | LPAREN ->
                    _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState164
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState164) : 'freshtv398)
            | DOT ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv399 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, (vty : 'tv_vartybind)) = _menhir_stack in
                let _v : 'tv_tybindseq = 
# 378 "specParser.mly"
                          ([vty])
# 4010 "specParser.ml"
                 in
                _menhir_goto_tybindseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv400)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : 'freshtv401 * _menhir_state * 'tv_vartybind) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv402)) : 'freshtv404)) : 'freshtv406)) : 'freshtv408)) : 'freshtv410)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ((('freshtv411 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4027 "specParser.ml"
            ))) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv412)) : 'freshtv414)
    | MenhirState129 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv423 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((assert (not _menhir_env._menhir_error);
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | PIPE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv415 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState206 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState206
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState206) : 'freshtv416)
        | RCURLY ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv419 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv417 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _, (ty : 'tv_tyd)) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_basety = 
# 316 "specParser.mly"
                              (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty, 
                Predicate.truee()))
# 4083 "specParser.ml"
             in
            _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv418)) : 'freshtv420)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv421 * _menhir_state) * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv422)) : 'freshtv424)
    | MenhirState247 | MenhirState238 | MenhirState115 | MenhirState234 | MenhirState128 | MenhirState214 | MenhirState216 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv427 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv425 * _menhir_state * 'tv_tyd) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (ty : 'tv_tyd)) = _menhir_stack in
        let _v : 'tv_basety = 
# 313 "specParser.mly"
                (RefinementType.Base ((Var.get_fresh_var "v"), 
                ty,
                Predicate.truee()))
# 4104 "specParser.ml"
         in
        _menhir_goto_basety _menhir_env _menhir_stack _menhir_s _v) : 'freshtv426)) : 'freshtv428)
    | _ ->
        _menhir_fail ()

and _menhir_reduce102 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4113 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack ->
    let (_menhir_stack, _menhir_s, (t : (
# 61 "specParser.mly"
        (string)
# 4119 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_tyd = 
# 308 "specParser.mly"
           (TyD.fromString t)
# 4124 "specParser.ml"
     in
    _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v

and _menhir_run124 : _menhir_env -> 'ttv_tail * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4131 "specParser.ml"
) -> (
# 61 "specParser.mly"
        (string)
# 4135 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv385 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4143 "specParser.ml"
    )) = Obj.magic _menhir_stack in
    let ((t2 : (
# 61 "specParser.mly"
        (string)
# 4148 "specParser.ml"
    )) : (
# 61 "specParser.mly"
        (string)
# 4152 "specParser.ml"
    )) = _v in
    ((let (_menhir_stack, _menhir_s, (t1 : (
# 61 "specParser.mly"
        (string)
# 4157 "specParser.ml"
    ))) = _menhir_stack in
    let _v : 'tv_tyd = 
# 307 "specParser.mly"
                  (TyD.Ty_param (TyD.fromString t1, TyD.fromString t2))
# 4162 "specParser.ml"
     in
    _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv386)

and _menhir_run4 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4169 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | OF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv379 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4181 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState5 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState5) : 'freshtv380)
    | PIPE | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv381 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4197 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 4202 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_tpatmatch = 
# 200 "specParser.mly"
              (Algebraic.Const {name=i;args=[]})
# 4207 "specParser.ml"
         in
        _menhir_goto_tpatmatch _menhir_env _menhir_stack _menhir_s _v) : 'freshtv382)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv383 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4217 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv384)

and _menhir_run17 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4225 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState17 _v
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv377 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4239 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 4244 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_params = 
# 184 "specParser.mly"
                ([RelId.fromString i])
# 4249 "specParser.ml"
         in
        _menhir_goto_params _menhir_env _menhir_stack _menhir_s _v) : 'freshtv378)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState17

and _menhir_run21 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv373) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 4269 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv365) = Obj.magic _menhir_stack in
            let (_v : (
# 61 "specParser.mly"
        (string)
# 4281 "specParser.ml"
            )) = _v in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv363) = Obj.magic _menhir_stack in
            let ((i : (
# 61 "specParser.mly"
        (string)
# 4289 "specParser.ml"
            )) : (
# 61 "specParser.mly"
        (string)
# 4293 "specParser.ml"
            )) = _v in
            ((let _v : 'tv_conargs = 
# 214 "specParser.mly"
               (Vector.fromList [Var.fromString i])
# 4298 "specParser.ml"
             in
            _menhir_goto_conargs _menhir_env _menhir_stack _v) : 'freshtv364)) : 'freshtv366)
        | LPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv367) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run24 _menhir_env (Obj.magic _menhir_stack) MenhirState23 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState23) : 'freshtv368)
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv369 * (
# 61 "specParser.mly"
        (string)
# 4318 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, (i : (
# 61 "specParser.mly"
        (string)
# 4323 "specParser.ml"
            ))) = _menhir_stack in
            let _v : 'tv_conpat = 
# 211 "specParser.mly"
               ((Tycon.fromString i, None))
# 4328 "specParser.ml"
             in
            _menhir_goto_conpat _menhir_env _menhir_stack _v) : 'freshtv370)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : 'freshtv371 * (
# 61 "specParser.mly"
        (string)
# 4338 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            (raise _eRR : 'freshtv372)) : 'freshtv374)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv375 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv376)

and _menhir_run83 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4352 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | EQUALOP ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv359 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4364 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState84 _v
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | LPAREN ->
            _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState84
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState84) : 'freshtv360)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv361 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4392 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv362)

and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4400 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState51
    | RBRACE | STAR ->
        _menhir_reduce34 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState51

and _menhir_run34 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)

and _menhir_run35 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState35 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState35
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState35

and _menhir_run102 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv355 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 4457 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | DOT ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv351 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4468 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState104 _v
            | LAMBDA ->
                _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | LPAREN ->
                _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | TRUE ->
                _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState104
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState104) : 'freshtv352)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv353 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4498 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv354)) : 'freshtv356)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv357 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv358)

and _menhir_run109 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 4513 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COMMA ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv345 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4525 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState110 _v
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState110) : 'freshtv346)
    | RPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv347 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4541 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, (i : (
# 61 "specParser.mly"
        (string)
# 4546 "specParser.ml"
        ))) = _menhir_stack in
        let _v : 'tv_paramseq = 
# 187 "specParser.mly"
                    ([RelId.fromString i])
# 4551 "specParser.ml"
         in
        _menhir_goto_paramseq _menhir_env _menhir_stack _menhir_s _v) : 'freshtv348)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv349 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 4561 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv350)

and _menhir_run134 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | CONJ | DISJ | IFF | IMPL | RCURLY | SEMICOLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv341 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        let _1 = () in
        let _v : 'tv_patom = 
# 341 "specParser.mly"
             (Predicate.truee())
# 4580 "specParser.ml"
         in
        _menhir_goto_patom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv342)
    | ARMINUS | CROSSPRD | EQUALOP | GREATERTHAN | MINUS | NUMEQ | PLUS | RPAREN | SUBSET | SUBSETEQ | UNION ->
        _menhir_reduce24 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv343 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv344)

and _menhir_run135 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState135 _v
    | LBRACE ->
        _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | LPAREN ->
        _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | NOT ->
        _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | TRUE ->
        _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState135
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState135

and _menhir_run136 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ANGLEFT ->
        _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | EXISTS ->
        _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState136 _v
    | LAMBDA ->
        _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | LBRACE ->
        _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | LPAREN ->
        _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | NOT ->
        _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | TRUE ->
        _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState136
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState136

and _menhir_run36 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv337 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState37
        | ID _v ->
            _menhir_run41 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState37 _v
        | RPAREN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv335 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState37 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | RCURLY ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv331 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv329 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                let _4 = () in
                let _3 = () in
                let _2 = () in
                let _1 = () in
                let _v : 'tv_ratom = 
# 240 "specParser.mly"
                                    (T(Vector.fromList []))
# 4695 "specParser.ml"
                 in
                _menhir_goto_ratom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv330)) : 'freshtv332)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv333 * _menhir_state)) * _menhir_state) = Obj.magic _menhir_stack in
                ((let (_menhir_stack, _menhir_s) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv334)) : 'freshtv336)
        | TRUE ->
            _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState37
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState37) : 'freshtv338)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv339 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv340)

and _menhir_run137 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv325 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 4731 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv301 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4742 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | CHARCONST _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv257 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4752 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 64 "specParser.mly"
       (string)
# 4757 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv253 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4768 "specParser.ml"
                    ))) * (
# 64 "specParser.mly"
       (string)
# 4772 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv251 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4779 "specParser.ml"
                    ))) * (
# 64 "specParser.mly"
       (string)
# 4783 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4788 "specParser.ml"
                    ))), (rhs : (
# 64 "specParser.mly"
       (string)
# 4792 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 364 "specParser.mly"
                                                    (
       				let rhstrimmed = String.get rhs 1 in 
       				 Predicate.BasePredicate.varCharEq 
                      (Var.fromString i1, rhstrimmed))
# 4803 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv252)) : 'freshtv254)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv255 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4813 "specParser.ml"
                    ))) * (
# 64 "specParser.mly"
       (string)
# 4817 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv256)) : 'freshtv258)
            | FALSE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv265 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4826 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv261 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4836 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv259 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4843 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4848 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 352 "specParser.mly"
                                           (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, false))
# 4858 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv260)) : 'freshtv262)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv263 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4868 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv264)) : 'freshtv266)
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv273 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4877 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 4882 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv269 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4893 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 4897 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv267 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4904 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 4908 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4913 "specParser.ml"
                    ))), (i2 : (
# 61 "specParser.mly"
        (string)
# 4917 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 348 "specParser.mly"
                                           (Predicate.BasePredicate.varEq 
                      (Var.fromString i1, Var.fromString i2))
# 4926 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv268)) : 'freshtv270)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv271 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4936 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 4940 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv272)) : 'freshtv274)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv281 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4949 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 62 "specParser.mly"
       (int)
# 4954 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv277 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4965 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 4969 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv275 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 4976 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 4980 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 4985 "specParser.ml"
                    ))), (rhs : (
# 62 "specParser.mly"
       (int)
# 4989 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 358 "specParser.mly"
                                              (Predicate.BasePredicate.varIntEq 
                      (Var.fromString i1, rhs))
# 4998 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv276)) : 'freshtv278)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv279 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5008 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 5012 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv280)) : 'freshtv282)
            | STRCONST _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv289 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5021 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 63 "specParser.mly"
       (string)
# 5026 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv285 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5037 "specParser.ml"
                    ))) * (
# 63 "specParser.mly"
       (string)
# 5041 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv283 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5048 "specParser.ml"
                    ))) * (
# 63 "specParser.mly"
       (string)
# 5052 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 5057 "specParser.ml"
                    ))), (rhs : (
# 63 "specParser.mly"
       (string)
# 5061 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 360 "specParser.mly"
                                                   (
       				let rhstrimmed = String.sub (rhs) (1) ((String.length rhs) - 2) in 
       				Predicate.BasePredicate.varStrEq 
                      (Var.fromString i1, rhstrimmed))
# 5072 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv284)) : 'freshtv286)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv287 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5082 "specParser.ml"
                    ))) * (
# 63 "specParser.mly"
       (string)
# 5086 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv288)) : 'freshtv290)
            | TRUE ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv297 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5095 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv293 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5105 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv291 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5112 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 5117 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _4 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 350 "specParser.mly"
                                          (Predicate.BasePredicate.varBoolEq 
                      (Var.fromString i1, true))
# 5127 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv292)) : 'freshtv294)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv295 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5137 "specParser.ml"
                    )))) = Obj.magic _menhir_stack in
                    ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv296)) : 'freshtv298)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv299 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5148 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv300)) : 'freshtv302)
        | GREATERTHAN ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv321 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5157 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv309 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5167 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 61 "specParser.mly"
        (string)
# 5172 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv305 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5183 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 5187 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv303 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5194 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 5198 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 5203 "specParser.ml"
                    ))), (i2 : (
# 61 "specParser.mly"
        (string)
# 5207 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 354 "specParser.mly"
                                                (Predicate.BasePredicate.varGt 
                      (Var.fromString i1, Var.fromString i2))
# 5216 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv304)) : 'freshtv306)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv307 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5226 "specParser.ml"
                    ))) * (
# 61 "specParser.mly"
        (string)
# 5230 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv308)) : 'freshtv310)
            | INT _v ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv317 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5239 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                let (_v : (
# 62 "specParser.mly"
       (int)
# 5244 "specParser.ml"
                )) = _v in
                ((let _menhir_stack = (_menhir_stack, _v) in
                let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | RBRACE ->
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv313 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5255 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 5259 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let _menhir_env = _menhir_discard _menhir_env in
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv311 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5266 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 5270 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), (i1 : (
# 61 "specParser.mly"
        (string)
# 5275 "specParser.ml"
                    ))), (rhs : (
# 62 "specParser.mly"
       (int)
# 5279 "specParser.ml"
                    ))) = _menhir_stack in
                    let _5 = () in
                    let _3 = () in
                    let _1 = () in
                    let _v : 'tv_bpatom = 
# 356 "specParser.mly"
                                                  (Predicate.BasePredicate.varIntGt 
                      (Var.fromString i1, rhs))
# 5288 "specParser.ml"
                     in
                    _menhir_goto_bpatom _menhir_env _menhir_stack _menhir_s _v) : 'freshtv312)) : 'freshtv314)
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    let (_menhir_env : _menhir_env) = _menhir_env in
                    let (_menhir_stack : ((('freshtv315 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5298 "specParser.ml"
                    ))) * (
# 62 "specParser.mly"
       (int)
# 5302 "specParser.ml"
                    )) = Obj.magic _menhir_stack in
                    ((let (((_menhir_stack, _menhir_s), _), _) = _menhir_stack in
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv316)) : 'freshtv318)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv319 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5313 "specParser.ml"
                ))) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv320)) : 'freshtv322)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv323 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5324 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv324)) : 'freshtv326)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv327 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv328)

and _menhir_run157 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState157
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState157

and _menhir_run40 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 62 "specParser.mly"
       (int)
# 5352 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv249) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((ii : (
# 62 "specParser.mly"
       (int)
# 5362 "specParser.ml"
    )) : (
# 62 "specParser.mly"
       (int)
# 5366 "specParser.ml"
    )) = _v in
    ((let _v : 'tv_elem = 
# 259 "specParser.mly"
              (Int(ii))
# 5371 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv250)

and _menhir_run49 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 5378 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LBRACE ->
        _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState49
    | LPAREN ->
        _menhir_reduce34 _menhir_env (Obj.magic _menhir_stack)
    | ANGRIGHT | ARMINUS | CONJ | CROSSPRD | DISJ | EQUALOP | GREATERTHAN | IFF | IMPL | MINUS | NUMEQ | PIPE | PLUS | RCURLY | RPAREN | SEMICOLON | SUBSET | SUBSETEQ | UNION ->
        _menhir_reduce26 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49

and _menhir_run42 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_env = _menhir_discard _menhir_env in
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv247) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    ((let f = () in
    let _v : 'tv_elem = 
# 261 "specParser.mly"
               (Bool(false))
# 5406 "specParser.ml"
     in
    _menhir_goto_elem _menhir_env _menhir_stack _menhir_s _v) : 'freshtv248)

and _menhir_run168 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | LPAREN ->
        _menhir_run158 _menhir_env (Obj.magic _menhir_stack) MenhirState168
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState168

and _menhir_run171 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | FALSE ->
        _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | ID _v ->
        _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
    | INT _v ->
        _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState171 _v
    | LCURLY ->
        _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | LPAREN ->
        _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | TRUE ->
        _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState171
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState171

and _menhir_run116 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run123 _menhir_env (Obj.magic _menhir_stack) MenhirState116 _v
    | LBRACE ->
        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | PRIME ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | REF ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState116
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState116

and _menhir_run117 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv243 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 5477 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv239 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5488 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            let (_v : (
# 61 "specParser.mly"
        (string)
# 5493 "specParser.ml"
            )) = _v in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv237 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5500 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            let ((t2 : (
# 61 "specParser.mly"
        (string)
# 5505 "specParser.ml"
            )) : (
# 61 "specParser.mly"
        (string)
# 5509 "specParser.ml"
            )) = _v in
            ((let ((_menhir_stack, _menhir_s), (t1 : (
# 61 "specParser.mly"
        (string)
# 5514 "specParser.ml"
            ))) = _menhir_stack in
            let _1 = () in
            let _v : 'tv_tyd = 
# 306 "specParser.mly"
                        (TyD.Ty_param (TyD.fromString ("`"^t1), TyD.fromString t2))
# 5520 "specParser.ml"
             in
            _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv238)) : 'freshtv240)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv241 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5530 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv242)) : 'freshtv244)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv245 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv246)

and _menhir_run126 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv235 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState126 in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 5555 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv231 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5566 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState128 _v
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | LCURLY ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | LPAREN ->
                _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | PRIME ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState128
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState128) : 'freshtv232)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv233 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5594 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv234)) : 'freshtv236)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState126

and _menhir_run129 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv229 * _menhir_state) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState129 in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 5616 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv225 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5627 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run123 _menhir_env (Obj.magic _menhir_stack) MenhirState131 _v
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState131
            | PRIME ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState131
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState131
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState131) : 'freshtv226)
        | ID _v ->
            _menhir_run124 _menhir_env (Obj.magic _menhir_stack) _v
        | PIPE | RCURLY ->
            _menhir_reduce102 _menhir_env (Obj.magic _menhir_stack)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv227 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5655 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv228)) : 'freshtv230)
    | LBRACE ->
        _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | PRIME ->
        _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | REF ->
        _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState129
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState129

and _menhir_run120 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv221 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 5682 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | RBRACE ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv217 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5693 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv215 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5700 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), (t : (
# 61 "specParser.mly"
        (string)
# 5705 "specParser.ml"
            ))) = _menhir_stack in
            let _3 = () in
            let _1 = () in
            let _v : 'tv_tyd = 
# 309 "specParser.mly"
                         (TyD.makeTList (TyD.fromString t))
# 5712 "specParser.ml"
             in
            _menhir_goto_tyd _menhir_env _menhir_stack _menhir_s _v) : 'freshtv216)) : 'freshtv218)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv219 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5722 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv220)) : 'freshtv222)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv223 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv224)

and _menhir_run209 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 5737 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run124 _menhir_env (Obj.magic _menhir_stack) _v
    | LCURLY ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv211 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5751 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ANGLEFT ->
            _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | EXISTS ->
            _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | FALSE ->
            _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | ID _v ->
            _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState210 _v
        | INT _v ->
            _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState210 _v
        | LAMBDA ->
            _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | LBRACE ->
            _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | LCURLY ->
            _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | LPAREN ->
            _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | NOT ->
            _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | TRUE ->
            _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState210
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState210) : 'freshtv212)
    | COMMA | RPAREN | SEMICOLON ->
        _menhir_reduce102 _menhir_env (Obj.magic _menhir_stack)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv213 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5791 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv214)

and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    match _menhir_s with
    | MenhirState258 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv63 * _menhir_state * 'tv_predspec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv64)
    | MenhirState256 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv65 * _menhir_state * 'tv_primdec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv66)
    | MenhirState254 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv67 * _menhir_state * 'tv_reldec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv68)
    | MenhirState252 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv69 * _menhir_state * 'tv_typedef)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv70)
    | MenhirState250 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv71 * _menhir_state * 'tv_typespec)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv72)
    | MenhirState247 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv73 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5829 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv74)
    | MenhirState242 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv75 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5838 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv76)
    | MenhirState238 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv77 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5847 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv78)
    | MenhirState234 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv79 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5856 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv80)
    | MenhirState232 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv81 * _menhir_state * 'tv_varty)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv82)
    | MenhirState223 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((((('freshtv83 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5870 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 5874 "specParser.ml"
        ))) * _menhir_state * 'tv_refty)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv84)
    | MenhirState216 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv85 * _menhir_state * 'tv_vartyatom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv86)
    | MenhirState214 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv87 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5888 "specParser.ml"
        ))) * _menhir_state * 'tv_pred)) * (
# 61 "specParser.mly"
        (string)
# 5892 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv88)
    | MenhirState210 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv89 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 5901 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv90)
    | MenhirState206 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv91 * _menhir_state) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv92)
    | MenhirState195 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv93 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv94)
    | MenhirState193 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv95 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv96)
    | MenhirState191 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv97 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv98)
    | MenhirState188 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv99 * _menhir_state * 'tv_patom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv100)
    | MenhirState184 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv101 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv102)
    | MenhirState182 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv103 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv104)
    | MenhirState180 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv105 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv106)
    | MenhirState178 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv107 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv108)
    | MenhirState176 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv109 * _menhir_state * 'tv_rexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv110)
    | MenhirState171 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv111 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv112)
    | MenhirState170 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv113 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv114)
    | MenhirState168 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv115 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv116)
    | MenhirState167 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv117 * _menhir_state) * _menhir_state * 'tv_tybindseq)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv118)
    | MenhirState164 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv119 * _menhir_state * 'tv_vartybind)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv120)
    | MenhirState160 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv121 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 5985 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv122)
    | MenhirState157 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv123 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv124)
    | MenhirState136 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv125 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv126)
    | MenhirState135 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv127 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv128)
    | MenhirState133 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv129 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6009 "specParser.ml"
        ))) * _menhir_state * 'tv_tyd)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv130)
    | MenhirState131 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv131 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6018 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv132)
    | MenhirState129 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv133 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv134)
    | MenhirState128 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv135 * _menhir_state) * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6032 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv136)
    | MenhirState126 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv137 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv138)
    | MenhirState116 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv139 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv140)
    | MenhirState115 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv141 * _menhir_state) * _menhir_state * 'tv_paramseq)) * (
# 61 "specParser.mly"
        (string)
# 6051 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s, _), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv142)
    | MenhirState110 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv143 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6060 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv144)
    | MenhirState108 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv145 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv146)
    | MenhirState104 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv147 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6074 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv148)
    | MenhirState101 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv149 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6083 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv150)
    | MenhirState94 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv151 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6092 "specParser.ml"
        )) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv152)
    | MenhirState93 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv153 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6101 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv154)
    | MenhirState91 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv155 * _menhir_state * 'tv_patmatch)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv156)
    | MenhirState86 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((((('freshtv157 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6115 "specParser.ml"
        )) * _menhir_state * 'tv_params)) * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv158)
    | MenhirState84 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv159 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6124 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv160)
    | MenhirState78 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv161 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv162)
    | MenhirState76 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv163 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv164)
    | MenhirState74 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv165 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv166)
    | MenhirState72 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv167 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv168)
    | MenhirState68 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv169 * _menhir_state * 'tv_funparam)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv170)
    | MenhirState62 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv171 * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv172)
    | MenhirState59 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv173 * _menhir_state * 'tv_ratom)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv174)
    | MenhirState54 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv175 * _menhir_state) * _menhir_state * 'tv_instexpr)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv176)
    | MenhirState51 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv177 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6173 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv178)
    | MenhirState50 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv179 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv180)
    | MenhirState49 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv181 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6187 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv182)
    | MenhirState47 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv183 * _menhir_state * 'tv_elem)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv184)
    | MenhirState37 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv185 * _menhir_state)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv186)
    | MenhirState35 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv187 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv188)
    | MenhirState33 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ((('freshtv189 * _menhir_state) * 'tv_conpat))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv190)
    | MenhirState25 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv191 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6216 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv192)
    | MenhirState23 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv193) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv194)
    | MenhirState20 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (((('freshtv195 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6229 "specParser.ml"
        )) * _menhir_state * 'tv_params)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv196)
    | MenhirState17 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv197 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6238 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv198)
    | MenhirState16 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv199 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6247 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv200)
    | MenhirState12 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv201 * _menhir_state * 'tv_tpatmatch)) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv202)
    | MenhirState7 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv203 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6261 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv204)
    | MenhirState5 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : ('freshtv205 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6270 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv206)
    | MenhirState3 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : (('freshtv207 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6279 "specParser.ml"
        ))) = Obj.magic _menhir_stack in
        ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv208)
    | MenhirState0 ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv209) = Obj.magic _menhir_stack in
        (raise _eRR : 'freshtv210)

and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv59 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6300 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv55 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6311 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run4 _menhir_env (Obj.magic _menhir_stack) MenhirState3 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState3) : 'freshtv56)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv57 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6329 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv58)) : 'freshtv60)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv61 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv62)

and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv45 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6353 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv43 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6364 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            let (_menhir_s : _menhir_state) = MenhirState93 in
            ((let _menhir_stack = (_menhir_stack, _menhir_s) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94) : 'freshtv44)
        | ID _v ->
            _menhir_run83 _menhir_env (Obj.magic _menhir_stack) MenhirState93 _v
        | LPAREN ->
            _menhir_run21 _menhir_env (Obj.magic _menhir_stack) MenhirState93
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState93) : 'freshtv46)
    | LPAREN ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv51 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv47 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_v : (
# 61 "specParser.mly"
        (string)
# 6397 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run17 _menhir_env (Obj.magic _menhir_stack) MenhirState16 _v
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState16) : 'freshtv48)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv49 * _menhir_state)) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv50)) : 'freshtv52)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv53 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv54)

and _menhir_run98 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | RELATION ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv39 * _menhir_state) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv35 * _menhir_state)) = Obj.magic _menhir_stack in
            let (_v : (
# 61 "specParser.mly"
        (string)
# 6442 "specParser.ml"
            )) = _v in
            ((let _menhir_stack = (_menhir_stack, _v) in
            let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | EQUALOP ->
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv31 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6453 "specParser.ml"
                )) = Obj.magic _menhir_stack in
                ((let _menhir_env = _menhir_discard _menhir_env in
                let _tok = _menhir_env._menhir_token in
                match _tok with
                | FALSE ->
                    _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | ID _v ->
                    _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
                | INT _v ->
                    _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState101 _v
                | LAMBDA ->
                    _menhir_run102 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | LCURLY ->
                    _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | LPAREN ->
                    _menhir_run35 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | TRUE ->
                    _menhir_run34 _menhir_env (Obj.magic _menhir_stack) MenhirState101
                | _ ->
                    assert (not _menhir_env._menhir_error);
                    _menhir_env._menhir_error <- true;
                    _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101) : 'freshtv32)
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                let (_menhir_env : _menhir_env) = _menhir_env in
                let (_menhir_stack : (('freshtv33 * _menhir_state)) * (
# 61 "specParser.mly"
        (string)
# 6483 "specParser.ml"
                )) = Obj.magic _menhir_stack in
                ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv34)) : 'freshtv36)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv37 * _menhir_state)) = Obj.magic _menhir_stack in
            ((let (_menhir_stack, _menhir_s) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv38)) : 'freshtv40)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv41 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv42)

and _menhir_run108 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        _menhir_run109 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108

and _menhir_run237 : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 61 "specParser.mly"
        (string)
# 6518 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | COLON ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv27 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6530 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | ID _v ->
            _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState238 _v
        | LBRACE ->
            _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | LCURLY ->
            _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | LPAREN ->
            _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | PRIME ->
            _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | REF ->
            _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState238
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState238) : 'freshtv28)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv29 * _menhir_state * (
# 61 "specParser.mly"
        (string)
# 6558 "specParser.ml"
        )) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s, _) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv30)

and _menhir_run240 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv23 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6575 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | EQUALOP ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv19 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6586 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ANGLEFT ->
                _menhir_run171 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | EXISTS ->
                _menhir_run168 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | FALSE ->
                _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | ID _v ->
                _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState242 _v
            | INT _v ->
                _menhir_run40 _menhir_env (Obj.magic _menhir_stack) MenhirState242 _v
            | LAMBDA ->
                _menhir_run157 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | LBRACE ->
                _menhir_run137 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | LCURLY ->
                _menhir_run36 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | LPAREN ->
                _menhir_run136 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | NOT ->
                _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | TRUE ->
                _menhir_run134 _menhir_env (Obj.magic _menhir_stack) MenhirState242
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState242) : 'freshtv20)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv21 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6624 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv22)) : 'freshtv24)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv25 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv26)

and _menhir_goto_start : _menhir_env -> 'ttv_tail -> _menhir_state -> (
# 77 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6639 "specParser.ml"
) -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s _v ->
    let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv17) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let (_v : (
# 77 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6648 "specParser.ml"
    )) = _v in
    ((let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv15) = Obj.magic _menhir_stack in
    let (_menhir_s : _menhir_state) = _menhir_s in
    let ((_1 : (
# 77 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6656 "specParser.ml"
    )) : (
# 77 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6660 "specParser.ml"
    )) = _v in
    (Obj.magic _1 : 'freshtv16)) : 'freshtv18)

and _menhir_run245 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
  fun _menhir_env _menhir_stack _menhir_s ->
    let _menhir_stack = (_menhir_stack, _menhir_s) in
    let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ID _v ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv11 * _menhir_state) = Obj.magic _menhir_stack in
        let (_v : (
# 61 "specParser.mly"
        (string)
# 6676 "specParser.ml"
        )) = _v in
        ((let _menhir_stack = (_menhir_stack, _v) in
        let _menhir_env = _menhir_discard _menhir_env in
        let _tok = _menhir_env._menhir_token in
        match _tok with
        | COLON ->
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv7 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6687 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let _menhir_env = _menhir_discard _menhir_env in
            let _tok = _menhir_env._menhir_token in
            match _tok with
            | ID _v ->
                _menhir_run209 _menhir_env (Obj.magic _menhir_stack) MenhirState247 _v
            | LBRACE ->
                _menhir_run120 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | LCURLY ->
                _menhir_run129 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | LPAREN ->
                _menhir_run126 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | PRIME ->
                _menhir_run117 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | REF ->
                _menhir_run116 _menhir_env (Obj.magic _menhir_stack) MenhirState247
            | _ ->
                assert (not _menhir_env._menhir_error);
                _menhir_env._menhir_error <- true;
                _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState247) : 'freshtv8)
        | _ ->
            assert (not _menhir_env._menhir_error);
            _menhir_env._menhir_error <- true;
            let (_menhir_env : _menhir_env) = _menhir_env in
            let (_menhir_stack : ('freshtv9 * _menhir_state) * (
# 61 "specParser.mly"
        (string)
# 6715 "specParser.ml"
            )) = Obj.magic _menhir_stack in
            ((let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
            _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv10)) : 'freshtv12)
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv13 * _menhir_state) = Obj.magic _menhir_stack in
        ((let (_menhir_stack, _menhir_s) = _menhir_stack in
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s) : 'freshtv14)

and _menhir_discard : _menhir_env -> _menhir_env =
  fun _menhir_env ->
    let lexer = _menhir_env._menhir_lexer in
    let lexbuf = _menhir_env._menhir_lexbuf in
    let _tok = lexer lexbuf in
    {
      _menhir_lexer = lexer;
      _menhir_lexbuf = lexbuf;
      _menhir_token = _tok;
      _menhir_error = false;
    }

and start : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (
# 77 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6742 "specParser.ml"
) =
  fun lexer lexbuf ->
    let _menhir_env =
      let (lexer : Lexing.lexbuf -> token) = lexer in
      let (lexbuf : Lexing.lexbuf) = lexbuf in
      ((let _tok = Obj.magic () in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_error = false;
      }) : _menhir_env)
    in
    Obj.magic (let (_menhir_env : _menhir_env) = _menhir_env in
    let (_menhir_stack : 'freshtv5) = ((), _menhir_env._menhir_lexbuf.Lexing.lex_curr_p) in
    ((let _menhir_env = _menhir_discard _menhir_env in
    let _tok = _menhir_env._menhir_token in
    match _tok with
    | ASSUME ->
        _menhir_run245 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | EOF ->
        let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv3) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = MenhirState0 in
        ((let (_menhir_env : _menhir_env) = _menhir_env in
        let (_menhir_stack : 'freshtv1) = Obj.magic _menhir_stack in
        let (_menhir_s : _menhir_state) = _menhir_s in
        ((let _1 = () in
        let _v : (
# 77 "specParser.mly"
       (SpecLang.RelSpec.t)
# 6774 "specParser.ml"
        ) = 
# 81 "specParser.mly"
              (RelSpec.mk_empty_relspec ())
# 6778 "specParser.ml"
         in
        _menhir_goto_start _menhir_env _menhir_stack _menhir_s _v) : 'freshtv2)) : 'freshtv4)
    | FORMULA ->
        _menhir_run240 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | ID _v ->
        _menhir_run237 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
    | LPAREN ->
        _menhir_run108 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | PRIMITIVE ->
        _menhir_run98 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | RELATION ->
        _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | TYPE ->
        _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0
    | _ ->
        assert (not _menhir_env._menhir_error);
        _menhir_env._menhir_error <- true;
        _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0) : 'freshtv6))

# 233 "/home/ashish/.opam/4.03.0/lib/menhir/standard.mly"
  

# 6801 "specParser.ml"
