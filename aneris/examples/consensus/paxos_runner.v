From aneris.examples.consensus Require Import
     paxos_prelude paxos_acceptor paxos_proposer paxos_learner paxos_client.

Definition runner (z1 z2 : Z) : expr :=
  let: "a1" := MakeAddress #"a1" #80 in
  let: "a2" := MakeAddress #"a2" #80 in
  let: "a3" := MakeAddress #"a3" #80 in
  let: "l1" := MakeAddress #"l1" #80 in
  let: "l2" := MakeAddress #"l2" #80 in
  let: "p1"  := MakeAddress #"p1" #80 in
  let: "p2"  := MakeAddress #"p2" #80 in
  let: "c" := MakeAddress #"c" #80 in
  let: "acceptors" := {[ "a1"; "a2"; "a3" ]} in
  let: "learners" := {[ "l1"; "l2" ]} in
  Start "a1" (acceptor int_serializer "learners" "a1");;
  Start "a2" (acceptor int_serializer "learners" "a2");;
  Start "a3" (acceptor int_serializer "learners" "a3");;
  Start "l1" (learner' int_serializer "acceptors" "l1" "c");;
  Start "l2" (learner' int_serializer "acceptors" "l2" "c");;
  Start "p1" (proposer' int_serializer "acceptors" "p1" #0 #2 #z1);;
  Start "p2" (proposer' int_serializer "acceptors" "p2" #1 #2 #z2);;
  Start "c" (client int_serializer "c").


Section runner.
  Definition p1_addr := SocketAddressInet "p1" 80.
  Definition p2_addr := SocketAddressInet "p2" 80.
  Definition a1_addr := SocketAddressInet "a1" 80.
  Definition a2_addr := SocketAddressInet "a2" 80.
  Definition a3_addr := SocketAddressInet "a3" 80.
  Definition l1_addr := SocketAddressInet "l1" 80.
  Definition l2_addr := SocketAddressInet "l2" 80.
  Definition c_addr  := SocketAddressInet "c" 80.

  Definition acceptors : gset socket_address := {[ a1_addr; a2_addr; a3_addr ]}.
  Definition proposers : gset socket_address := {[ p1_addr; p2_addr ]}.
  Definition learners : gset socket_address := {[ l1_addr; l2_addr ]}.
  Definition addrs : gset socket_address := acceptors ∪ proposers ∪ learners ∪ {[c_addr]}.

  Definition ips : gset string := {[ "p1"; "p2"; "a1"; "a2"; "a3"; "l1"; "l2"; "c" ]}.

  Definition values : gset Z := {[ 41; 42 ]}%Z.

  Global Program Instance runner_topo : network_topo :=
    Build_network_topo acceptors proposers learners values _ _ _ _.
  Solve All Obligations with rewrite ?size_union ?size_singleton //; set_solver.

  Context `{!paxosG Σ runner_topo}.
  Context `{anerisG (Paxos_model runner_topo) Σ}.

  Section NotSymbolic.

    Fixpoint reduce_wp_aux (n : nat) :
      expr → (expr → Prop) → (val → Prop) → Prop :=
      match n with
      | O   => fun e Ψ Φ => Ψ e
      | S n =>
          fix go (e : expr) (Ψ : expr → Prop) (Φ : val → Prop) {struct e} : Prop :=
        match e with
        | Val v => Φ v
        | Pair e1 e2 =>
            go e2
              (fun e2' => Ψ (Pair e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (Pair e1' (Val v2)))
                   (fun v1  => Φ (PairV v1 v2)))
        | App e1 e2 =>
            go e2
              (fun e2' => Ψ (App e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (App e1' (Val v2)))
                   (fun v1  =>
                      match v1 with
                      | RecV f x e3 =>
                          reduce_wp_aux n
                            (subst' x v2 (subst' f (RecV f x e3) e3)) Ψ Φ
                      | _ => Ψ (App (Val v1) (Val v2))
                      end))
        | Store e1 e2 =>
            go e2
              (fun e2' => Ψ (Store e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (Store e1' (Val v2)))
                   (fun v1  => Ψ (Store (Val v1) (Val v2))))
        | BinOp op e1 e2 =>
            go e2
              (fun e2' => Ψ (BinOp op e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (BinOp op e1' (Val v2)))
                   (fun v1 =>
                      match bin_op_eval op v1 v2 with
                      | Some v => Φ v
                      | None => Ψ (BinOp op (Val v1) (Val v2))
                      end))
        | Match e0 x1 e1 x2 e2 =>
            go e0
              (fun e0' => Ψ (Match e0' x1 e1 x2 e2))
              (fun v0 =>
                 match v0 with
                 | InjLV v => reduce_wp_aux n (subst' x1 v e1) Ψ Φ
                 | InjRV v => reduce_wp_aux n (subst' x2 v e2) Ψ Φ
                 | _       => Ψ (Match (Val v0) x1 e1 x2 e2)
                 end)
        | Snd (Val (PairV v1 v2)) => Φ v2
        | Rec f x e => Φ (RecV f x e)
        | MakeAddress (Val (LitV (LitString s))) (Val (LitV (LitInt p))) =>
            Φ (LitV (LitSocketAddress (SocketAddressInet s (Z.to_pos p))))
        | _ => Ψ e
        end
      end.

    Definition reduce_wp (E : environments.envs (iProp Σ))
      (ip : ip_address) (e : expr) (Φ : val → iProp Σ) : Prop :=
      reduce_wp_aux 8 e
        (fun e' => environments.envs_entails E (aneris_wp ip top e' Φ))
        (fun v => environments.envs_entails E (fupd top top (Φ v))).
    Arguments reduce_wp E ip e Φ /.

    Lemma reduce_wp_sound (E : environments.envs (iProp Σ))
      (ip : ip_address) (e : expr) (Φ : val → iProp Σ) :
      reduce_wp E ip e (fun v => Φ v) →
      environments.envs_entails E (aneris_wp ip top e Φ).
    Proof. Admitted.

    Ltac sk_pures :=
      simple apply reduce_wp_sound;
      cbv [reduce_wp reduce_wp_aux bin_op_eval decide decide_rel bin_op_eq_dec
             bin_op_rec bin_op_rect fmap bin_op_eval_int option_fmap option_map
             subst subst' id string_eq_dec string_rec and_dec string_rect
             sumbool_rec sumbool_rect not_dec ascii_eq_dec eq_ind_r
             Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect bool_dec
             bool_rec bool_rect binder_dec_eq binder_rec binder_rect].

  End NotSymbolic.

  Section Symbolic.

    Inductive sexpr : Set :=
    | SMeta : expr → sexpr
    | SVal : sval → sexpr
    | SVar : string → sexpr
    | SRec : binder → binder → sexpr → sexpr
    | SApp : sexpr → sexpr → sexpr
    | SBinOp : bin_op → sexpr → sexpr → sexpr
    | SIf : sexpr → sexpr → sexpr → sexpr
    | SPair : sexpr → sexpr → sexpr
    | SFst : sexpr → sexpr
    | SSnd : sexpr → sexpr
    | SInjL : sexpr → sexpr
    | SInjR : sexpr → sexpr
    | SCase : sexpr → sexpr → sexpr → sexpr
    | SLoad : sexpr → sexpr
    | SStore : sexpr → sexpr → sexpr
    | SMakeAddress : sexpr → sexpr → sexpr
    with sval : Set :=
    | SMetaV : val -> sval
    | SLitV : base_lit → sval
    | SRecV : binder → binder → sexpr → sval
    | SPairV : sval → sval → sval
    | SInjLV : sval → sval
    | SInjRV : sval → sval.

    Notation SLam x e := (SRec BAnon x e) (only parsing).
    Notation SLet x e1 e2 := (SApp (SLam x e2) e1) (only parsing).
    Notation SSeq e1 e2 := (SLet BAnon e1 e2) (only parsing).
    Notation SMatch e0 x1 e1 x2 e2 := (SCase e0 (SLam x1 e1) (SLam x2 e2)) (only parsing).

    Fixpoint denote (e : sexpr) : expr :=
      match e with
      | SMeta e => e
      | SVal v => Val (denoteV v)
      | SVar x => Var x
      | SRec f x e => Rec f x (denote e)
      | SApp e1 e2 => App (denote e1) (denote e2)
      | SBinOp op e1 e2 => BinOp op (denote e1) (denote e2)
      | SIf e1 e2 e3 => If (denote e1) (denote e2) (denote e3)
      | SPair e1 e2 => Pair (denote e1) (denote e2)
      | SFst e => Fst (denote e)
      | SSnd e => Snd (denote e)
      | SInjL e => InjL (denote e)
      | SInjR e => InjR (denote e)
      | SCase e1 e2 e3 => Case (denote e1) (denote e2) (denote e3)
      | SLoad e => Load (denote e)
      | SStore e1 e2 => Store (denote e1) (denote e2)
      | SMakeAddress e1 e2 => MakeAddress (denote e1) (denote e2)
      end
    with
    denoteV (v : sval) : val :=
      match v with
      | SMetaV v => v
      | SLitV v => LitV v
      | SRecV f x e => RecV f x (denote e)
      | SPairV v1 v2 => PairV (denoteV v1) (denoteV v2)
      | SInjLV v => InjLV (denoteV v)
      | SInjRV v => InjRV (denoteV v)
      end.

    Fixpoint ssubst (x : string) (v : sval) (e : sexpr) {struct e} : sexpr :=
      match e with
      | SMeta e0 => SMeta (subst x (denoteV v) e0)
      | SVal v => SVal v
      | SVar y => if decide (x = y) then SVal v else SVar y
      | SRec f y e0 =>
          SRec f y
            (if decide (and (not (eq (BNamed x) f)) (not (eq (BNamed x) y)))
             then ssubst x v e0
             else e0)
      | SApp e1 e2 => SApp (ssubst x v e1) (ssubst x v e2)
      | SBinOp op e1 e2 => SBinOp op (ssubst x v e1) (ssubst x v e2)
      | SIf e1 e2 e3 => SIf (ssubst x v e1) (ssubst x v e2) (ssubst x v e3)
      | SPair e1 e2 => SPair (ssubst x v e1) (ssubst x v e2)
      | SFst e => SFst (ssubst x v e)
      | SSnd e => SSnd (ssubst x v e)
      | SInjL e => SInjL (ssubst x v e)
      | SInjR e => SInjR (ssubst x v e)
      | SCase e1 e2 e3 => SCase (ssubst x v e1) (ssubst x v e2) (ssubst x v e3)
      | SLoad e => SLoad (ssubst x v e)
      | SStore e1 e2 => SStore (ssubst x v e1) (ssubst x v e2)
      | SMakeAddress e1 e2 => SMakeAddress (ssubst x v e1) (ssubst x v e2)
      end.

    Definition ssubst' (mx : binder) (v : sval) : sexpr → sexpr :=
      match mx with
      | BAnon => id
      | BNamed x => ssubst x v
      end.

    Fixpoint symbolic_reduce_wp_aux (n : nat) :
      sexpr → (sexpr → nat → Prop) → (sval → nat → Prop) → nat → Prop :=
      match n with
      | O   => fun e Ψ Φ => Ψ e
      | S n => fix go (e : sexpr) (Ψ : sexpr → nat → Prop)
                 (Φ : sval → nat → Prop) (nsteps : nat) {struct e} : Prop :=
        match e with
        | SMeta e => Ψ (SMeta e) nsteps
        | SVal v => Φ v nsteps
        | SPair e1 e2 =>
            go e2
              (fun e2' => Ψ (SPair e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (SPair e1' (SVal v2)))
                   (fun v1  => Φ (SPairV v1 v2))) nsteps
        | SApp e1 e2 =>
            go e2
              (fun e2' nsteps => Ψ (SApp e1 e2') nsteps)
              (fun v2 =>
                 go e1
                   (fun e1' nsteps => Ψ (SApp e1' (SVal v2)) nsteps)
                   (fun v1 nsteps =>
                      match v1 with
                      | SRecV f x e3 =>
                          symbolic_reduce_wp_aux n
                            (ssubst' x v2 (ssubst' f (SRecV f x e3) e3)) Ψ Φ (S nsteps)
                      | _ => Ψ (SApp (SVal v1) (SVal v2)) nsteps
                      end)) nsteps
        | SStore e1 e2 =>
            go e2
              (fun e2' => Ψ (SStore e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (SStore e1' (SVal v2)))
                   (fun v1  => Ψ (SStore (SVal v1) (SVal v2)))) nsteps
        | SBinOp op e1 e2 =>
            go e2
              (fun e2' => Ψ (SBinOp op e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (SBinOp op e1' (SVal v2)))
                   (fun v1 nsteps =>
                      match bin_op_eval op (denoteV v1) (denoteV v2) with
                      | Some v => Φ (SMetaV v) (S nsteps)
                      | None => Ψ (SBinOp op (SVal v1) (SVal v2)) nsteps
                      end)) nsteps
        | SMatch e0 x1 e1 x2 e2 =>
            go e0
              (fun e0' => Ψ (SMatch e0' x1 e1 x2 e2))
              (fun v0 nsteps =>
                 match v0 with
                 | SInjLV v => symbolic_reduce_wp_aux n (ssubst' x1 v e1) Ψ Φ (S nsteps)
                 | SInjRV v => symbolic_reduce_wp_aux n (ssubst' x2 v e2) Ψ Φ (S nsteps)
                 | _        => Ψ (SMatch (SVal v0) x1 e1 x2 e2) nsteps
                 end) nsteps
        | SSnd (SVal (SPairV v1 v2)) => Φ v2 (S nsteps)
        | SRec f x e => Φ (SRecV f x e) (S nsteps)
        | SMakeAddress (SVal (SLitV (LitString s))) (SVal (SLitV (LitInt p))) =>
            Φ (SLitV (LitSocketAddress (SocketAddressInet s (Z.to_pos p)))) (S nsteps)
        | _ => Ψ e nsteps
        end
      end.

    Definition symbolic_reduce_wp (E : environments.envs (iProp Σ))
      (ip : ip_address) (e : sexpr) (Φ : val → iProp Σ) : Prop :=
      symbolic_reduce_wp_aux 20 e
        (fun e' steps => environments.envs_entails E (aneris_wp ip top (denote e') Φ))
        (fun v steps => environments.envs_entails E (fupd top top (Φ (denoteV v))))
        (* Start with 0 steps *)
        0.
    #[global] Arguments symbolic_reduce_wp E ip e Φ /.

    Lemma symbolic_reduce_wp_sound (E : environments.envs (iProp Σ))
      (ip : ip_address) (e : sexpr) (Φ : val → iProp Σ) :
      symbolic_reduce_wp E ip e Φ ->
      environments.envs_entails E (aneris_wp ip top (denote e) Φ).
    Proof. Admitted.

  End Symbolic.

  Ltac sreify :=
    change_no_check
      (aneris_wp ?s ?m ?e ?Φ) with
      (aneris_wp s m (denote (SMeta e)) Φ);
    repeat
      (try change_no_check (SMeta (App ?e1 ?e2)) with (SApp (SMeta e1) (SMeta e2));
       try change_no_check (SMeta (Rec ?f ?x ?e)) with (SRec f x (SMeta e));
       try change_no_check (SMeta (MakeAddress ?e1 ?e2)) with (SMakeAddress (SMeta e1) (SMeta e2));
       try change_no_check (SMeta (Val ?v)) with (SVal (SMetaV v));
       try change_no_check (SMetaV (LitV ?v)) with (SLitV v);
       try change_no_check (SMeta (Var ?x)) with (SVar x)
      );
    change ?x with x.

  Ltac swp_pures :=
    sreify;
    simple apply symbolic_reduce_wp_sound;
    simpl.
  (* cbv [symbolic_reduce_wp *)
  (*        symbolic_reduce_wp_aux *)
  (*        bin_op_eval decide denote denoteV *)
  (*        decide_rel bin_op_eq_dec *)
  (*        bin_op_rec bin_op_rect fmap bin_op_eval_int option_fmap option_map *)
  (*        ssubst ssubst' *)
  (*        subst subst' id string_eq_dec string_rec and_dec string_rect *)
  (*        sumbool_rec sumbool_rect not_dec ascii_eq_dec eq_ind_r *)
  (*        Ascii.ascii_dec Ascii.ascii_rec Ascii.ascii_rect bool_dec *)
  (*        bool_rec bool_rect binder_dec_eq binder_rec binder_rect]. *)

  Section NewSymbolic.

    Inductive nsexpr : Set :=
    | NSMeta : list (string * nsval) → nat → nsexpr
    | NSVal : nsval → nsexpr
    | NSVar : string → nsexpr
    | NSRec : binder → binder → nsexpr → nsexpr
    | NSApp : nsexpr → nsexpr → nsexpr
    | NSBinOp : bin_op → nsexpr → nsexpr → nsexpr
    | NSIf : nsexpr → nsexpr → nsexpr → nsexpr
    | NSPair : nsexpr → nsexpr → nsexpr
    | NSFst : nsexpr → nsexpr
    | NSSnd : nsexpr → nsexpr
    | NSInjL : nsexpr → nsexpr
    | NSInjR : nsexpr → nsexpr
    | NSCase : nsexpr → nsexpr → nsexpr → nsexpr
    | NSLoad : nsexpr → nsexpr
    | NSStore : nsexpr → nsexpr → nsexpr
    | NSMakeAddress : nsexpr → nsexpr → nsexpr
    | NSStart : base_lit → nsexpr → nsexpr
    with nsval : Set :=
    | NSMetaV : nat -> nsval
    | NSLitV : base_lit → nsval
    | NSRecV : binder → binder → nsexpr → nsval
    | NSPairV : nsval → nsval → nsval
    | NSInjLV : nsval → nsval
    | NSInjRV : nsval → nsval.

    Notation NSLam x e := (NSRec BAnon x e) (only parsing).
    Notation NSLet x e1 e2 := (NSApp (NSLam x e2) e1) (only parsing).
    Notation NSSeq e1 e2 := (NSLet BAnon e1 e2) (only parsing).
    Notation NSMatch e0 x1 e1 x2 e2 := (NSCase e0 (NSLam x1 e1) (NSLam x2 e2)) (only parsing).

    Notation NSubst := (list (string * nsval)).
    Notation Subst := (list (string * val)).

    Fixpoint substs (s : Subst) (e : expr) {struct s} : expr :=
      match s with
      | nil => e
      | cons (x,v) s' => subst' x v (substs s' e)
      end.

    Section Denote.

      Context (emap : list expr) (vmap : list val).

      Definition ndenoteS (ndenoteV : nsval -> val) : NSubst -> Subst :=
        fix ndenoteS (s : NSubst) {struct s} : Subst :=
          match s with
          | nil => nil
          | cons (x, v) s' => cons (x, ndenoteV v) (ndenoteS s')
          end.

      Fixpoint ndenote (e : nsexpr) : expr :=
        match e with
        | NSMeta s n => match nth_error emap n with
                        | Some e1 => substs (ndenoteS ndenoteV s) e1
                        | None => #()
                        end
        | NSVal v => Val (ndenoteV v)
        | NSVar x => Var x
        | NSRec f x e1 => Rec f x (ndenote e1)
        | NSApp e1 e2 => App (ndenote e1) (ndenote e2)
        | NSBinOp op e1 e2 => BinOp op (ndenote e1) (ndenote e2)
        | NSIf e1 e2 e3 => If (ndenote e1) (ndenote e2) (ndenote e3)
        | NSPair e1 e2 => Pair (ndenote e1) (ndenote e2)
        | NSFst e1 => Fst (ndenote e1)
        | NSSnd e1 => Snd (ndenote e1)
        | NSInjL e1 => InjL (ndenote e1)
        | NSInjR e1 => InjR (ndenote e1)
        | NSCase e1 e2 e3 => Case (ndenote e1) (ndenote e2) (ndenote e3)
        | NSLoad e1 => Load (ndenote e1)
        | NSStore e1 e2 => Store (ndenote e1) (ndenote e2)
        | NSMakeAddress e1 e2 => MakeAddress (ndenote e1) (ndenote e2)
        | NSStart b e1 => Start b (ndenote e1)
        end
      with
      ndenoteV (v : nsval) : val :=
        match v with
        | NSMetaV n => match nth_error vmap n with
                       | Some v1 => v1
                       | None => #()
                       end
        | NSLitV v1 => LitV v1
        | NSRecV f x e => RecV f x (ndenote e)
        | NSPairV v1 v2 => PairV (ndenoteV v1) (ndenoteV v2)
        | NSInjLV v1 => InjLV (ndenoteV v1)
        | NSInjRV v1 => InjRV (ndenoteV v1)
        end.

    End Denote.
    #[global] Arguments ndenote _ _ _ /.

    Fixpoint nssubst (x : string) (v : nsval) (e : nsexpr) {struct e} : nsexpr :=
      match e with
      | NSMeta s n => NSMeta (cons (x,v) s) n
      | NSVal v => NSVal v
      | NSVar y => if decide (x = y) then NSVal v else NSVar y
      | NSRec f y e0 =>
          NSRec f y
            (if decide (and (not (eq (BNamed x) f)) (not (eq (BNamed x) y)))
             then nssubst x v e0
             else e0)
      | NSApp e1 e2 => NSApp (nssubst x v e1) (nssubst x v e2)
      | NSBinOp op e1 e2 => NSBinOp op (nssubst x v e1) (nssubst x v e2)
      | NSIf e1 e2 e3 => NSIf (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
      | NSPair e1 e2 => NSPair (nssubst x v e1) (nssubst x v e2)
      | NSFst e => NSFst (nssubst x v e)
      | NSSnd e => NSSnd (nssubst x v e)
      | NSInjL e => NSInjL (nssubst x v e)
      | NSInjR e => NSInjR (nssubst x v e)
      | NSCase e1 e2 e3 => NSCase (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
      | NSLoad e => NSLoad (nssubst x v e)
      | NSStore e1 e2 => NSStore (nssubst x v e1) (nssubst x v e2)
      | NSMakeAddress e1 e2 => NSMakeAddress (nssubst x v e1) (nssubst x v e2)
      | NSStart b e1 => NSStart b (nssubst x v e1)
      end.

    Definition nssubst' (mx : binder) (v : nsval) : nsexpr → nsexpr :=
      match mx with
      | BAnon => id
      | BNamed x => nssubst x v
      end.

    Fixpoint reduce_aux (n : nat) : nsexpr → nsexpr + nsval :=
      match n with
      | O   => inl
      | S n =>
          fix go (e : nsexpr) {struct e} :=
            match e with
            | NSMeta s n   => inl e
            | NSVal v      => inr v
            | NSPair e1 e2 =>
                match go e2 with
                | inl e2' => inl (NSPair e1 e2')
                | inr v2  =>
                    match go e1 with
                    | inl e1' => inl (NSPair e1' (NSVal v2))
                    | inr v1  => inr (NSPairV v1 v2)
                    end
                end
            | NSApp e1 e2 =>
                match go e2 with
                | inl e2' => inl (NSApp e1 e2')
                | inr v2 =>
                    match go e1 with
                    | inl e1' => inl (NSApp e1' (NSVal v2))
                    | inr v1  =>
                        match v1 with
                        | NSRecV f x e3 =>
                            reduce_aux n
                              (nssubst' x v2 (nssubst' f (NSRecV f x e3) e3))
                        | _ => inl (NSApp (NSVal v1) (NSVal v2))
                        end
                    end
                end
            | NSStore e1 e2 =>
                match go e2 with
                | inl e2' => inl (NSStore e1 e2')
                | inr v2  => match go e1 with
                             | inl e1' => inl (NSStore e1' (NSVal v2))
                             | inr v1  => inl (NSStore (NSVal v1) (NSVal v2))
                             end
                end
            | NSBinOp op e1 e2 =>
                match go e2 with
                | inl e2' => inl (NSBinOp op e1 e2')
                | inr v2  =>
                    match go e1 with
                    | inl e1' => inl (NSBinOp op e1' (NSVal v2))
                    | inr v1  => (* TODO: perform reductions here *)
                                 inl (NSBinOp op (NSVal v1) (NSVal v2))
                    end
                end
            | NSMatch e0 x1 e1 x2 e2 =>
                match go e0 with
                | inl e0' => inl (NSMatch e0' x1 e1 x2 e2)
                | inr v0  =>
                    match v0 with
                    | NSInjLV v => reduce_aux n (nssubst' x1 v e1)
                    | NSInjRV v => reduce_aux n (nssubst' x2 v e2)
                    | _         => inl (NSMatch (NSVal v0) x1 e1 x2 e2)
                    end
                end
            | NSSnd (NSVal (NSPairV v1 v2)) => inr v2
            | NSRec f x e => inr (NSRecV f x e)
            | NSMakeAddress (NSVal (NSLitV (LitString s))) (NSVal (NSLitV (LitInt p))) =>
                inr (NSLitV (LitSocketAddress (SocketAddressInet s (Z.to_pos p))))
            | _ => inl e
            end
      end.

    Definition reduce (e : nsexpr) : nsexpr :=
      match reduce_aux 10 e with
      | inl e' => e'
      | inr v  => NSVal v
      end.
    #[global] Arguments reduce e /.

    Lemma reduce_sound (E : environments.envs (iProp Σ))
      (ip : ip_address) (emap : list expr) (vmap : list val) (e : nsexpr) (Φ : val → iProp Σ) :
      forall e',
      reduce e = e' ->
      environments.envs_entails E (aneris_wp ip top (ndenote emap vmap e') Φ) ->
      environments.envs_entails E (aneris_wp ip top (ndenote emap vmap e) Φ).
    Proof. Admitted.

    Fixpoint nsymbolic_reduce_wp_aux (n : nat) :
      nsexpr → (nsexpr → nat → Prop) → (nsval → nat → Prop) → nat → Prop :=
      match n with
      | O   => fun e Ψ Φ => Ψ e
      | S n => fix go (e : nsexpr) (Ψ : nsexpr → nat → Prop)
                 (Φ : nsval → nat → Prop) (nsteps : nat) {struct e} : Prop :=
        match e with
        | NSMeta s n => Ψ (NSMeta s n) nsteps
        | NSVal v => Φ v nsteps
        | NSPair e1 e2 =>
            go e2
              (fun e2' => Ψ (NSPair e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (NSPair e1' (NSVal v2)))
                   (fun v1  => Φ (NSPairV v1 v2))) nsteps
        | NSApp e1 e2 =>
            go e2
              (fun e2' nsteps => Ψ (NSApp e1 e2') nsteps)
              (fun v2 =>
                 go e1
                   (fun e1' nsteps => Ψ (NSApp e1' (NSVal v2)) nsteps)
                   (fun v1 nsteps =>
                      match v1 with
                      | NSRecV f x e3 =>
                          nsymbolic_reduce_wp_aux n
                            (nssubst' x v2 (nssubst' f (NSRecV f x e3) e3)) Ψ Φ (S nsteps)
                      | _ => Ψ (NSApp (NSVal v1) (NSVal v2)) nsteps
                      end)) nsteps
        | NSStore e1 e2 =>
            go e2
              (fun e2' => Ψ (NSStore e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (NSStore e1' (NSVal v2)))
                   (fun v1  => Ψ (NSStore (NSVal v1) (NSVal v2)))) nsteps
        | NSBinOp op e1 e2 =>
            go e2
              (fun e2' => Ψ (NSBinOp op e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (NSBinOp op e1' (NSVal v2)))
                   (fun v1 nsteps =>
                      (* TODO: The concrete reduction of values requires plugging
                         *)
                      (* match bin_op_eval op (ndenoteV v1) (ndenoteV v2) with *)
                      (* | Some v => Φ (NSMetaV v) (S nsteps) *)
                      (* | None => Ψ (NSBinOp op (NSVal v1) (NSVal v2)) nsteps *)
                      (* end *)
                      Ψ (NSBinOp op (NSVal v1) (NSVal v2)) nsteps))
              nsteps
        | NSMatch e0 x1 e1 x2 e2 =>
            go e0
              (fun e0' => Ψ (NSMatch e0' x1 e1 x2 e2))
              (fun v0 nsteps =>
                 match v0 with
                 | NSInjLV v => nsymbolic_reduce_wp_aux n (nssubst' x1 v e1) Ψ Φ (S nsteps)
                 | NSInjRV v => nsymbolic_reduce_wp_aux n (nssubst' x2 v e2) Ψ Φ (S nsteps)
                 | _         => Ψ (NSMatch (NSVal v0) x1 e1 x2 e2) nsteps
                 end) nsteps
        | NSSnd (NSVal (NSPairV v1 v2)) => Φ v2 (S nsteps)
        | NSRec f x e => Φ (NSRecV f x e) (S nsteps)
        | NSMakeAddress (NSVal (NSLitV (LitString s))) (NSVal (NSLitV (LitInt p))) =>
            Φ (NSLitV (LitSocketAddress (SocketAddressInet s (Z.to_pos p)))) (S nsteps)
        | _ => Ψ e nsteps
        end
      end.

    Definition nsymbolic_reduce_wp (E : environments.envs (iProp Σ))
      (ip : ip_address) (emap : list expr) (vmap : list val) (e : nsexpr) (Φ : val → iProp Σ) : Prop :=
      nsymbolic_reduce_wp_aux 20 e
        (fun e' steps => environments.envs_entails E (aneris_wp ip top (ndenote emap vmap e') Φ))
        (fun v steps => environments.envs_entails E (fupd top top (Φ (ndenoteV emap vmap v))))
        (* Start with 0 steps *)
        0.
    #[global] Arguments nsymbolic_reduce_wp E ip emap vmap e Φ /.

    Lemma nsymbolic_reduce_wp_sound (E : environments.envs (iProp Σ))
      (ip : ip_address) (emap : list expr) (vmap : list val) (e : nsexpr) (Φ : val → iProp Σ) :
      nsymbolic_reduce_wp E ip emap vmap e Φ ->
      environments.envs_entails E (aneris_wp ip top (ndenote emap vmap e) Φ).
    Proof. Admitted.

    Ltac inList x xs :=
      match xs with
      | @nil _         => false
      | @cons _ x _    => true
      | @cons _ _ ?xs' => inList x xs'
      end.

    Ltac addToEMap e emap :=
      let b := inList e emap in
      match b with
      | true => emap
      | false => constr:(@cons expr e emap)
      end.

    Ltac addToVMap v vmap :=
      let b := inList v vmap in
      match b with
      | true => vmap
      | false => constr:(@cons val v vmap)
      end.

    Ltac mkMapExpr
      emap0 (* : list expr *)
      vmap0 (* : list val *)
      e0    (* : expr *)
      tac0  (* : list expr -> list val -> r *)
            (* : r *)
      :=
      let rec mkMapExpr emap vmap e tac :=
        (* idtac "mkMapExpr" emap vmap e; *)
        lazymatch e with
        | Val ?v =>
            mkMapVal emap vmap v tac
        | Var ?x =>
            (* TODO: We do not allow meta-variables inside strings,
               so should we check if x is ground? *)
            tac emap vmap
        | Rec ?b1 ?b2 ?e1 =>
            mkMapExpr emap vmap e1 tac
        | App ?e1 ?e2 =>
            mkMapExpr emap vmap e1 ltac:(fun emap1 vmap1 =>
            mkMapExpr emap1 vmap1 e2 tac)
        | MakeAddress ?e1 ?e2 =>
            mkMapExpr emap vmap e1 ltac:(fun emap1 vmap1 =>
            mkMapExpr emap1 vmap1 e2 tac)
        | Start ?b ?e1 =>
            mkMapExpr emap vmap e1 tac
        | _      =>
            (* idtac "mkMapExpr.default.beforeAddToEMap" emap; *)
            let emap' := addToEMap e emap in
            (* idtac "mkMapExpr.default.afterAddToEMap" emap'; *)
            tac emap' vmap
        end
      with mkMapVal emap vmap v tac :=
        lazymatch v with
        | LitV ?b =>
            (* TODO: We do not allow meta-variables inside base_lits,
               so should we check if b is ground? *)
            tac emap vmap
        | _ =>
            let vmap' := addToVMap v vmap in
            tac emap vmap'
        end
      in mkMapExpr emap0 vmap0 e0 tac0.

    Ltac lookup
      (* forall a. *)
      x  (* : a *)
      xs (* : list a *)
         (* : nat *)
      := lazymatch xs with
         | @cons _ x _    => O
         | @cons _ _ ?xs' =>
             let n := lookup x xs' in
             constr:(S n)
         end.

    Ltac reifyExpr emap vmap e0 :=
      let rec reifyExpr e :=
        lazymatch e with
        | Val ?v =>
            let nsv := reifyVal v in
            constr:(NSVal nsv)
        | Var ?x =>
            constr:(NSVar x)
        | Rec ?b1 ?b2 ?e1 =>
            let nse1 := reifyExpr e1 in
            constr:(NSRec b1 b2 nse1)
        | App ?e1 ?e2 =>
            let nse1 := reifyExpr e1 in
            let nse2 := reifyExpr e2 in
            constr:(NSApp nse1 nse2)
        | MakeAddress ?e1 ?e2 =>
            let nse1 := reifyExpr e1 in
            let nse2 := reifyExpr e2 in
            constr:(NSMakeAddress nse1 nse2)
        | Start ?b ?e1 =>
            let nse1 := reifyExpr e1 in
            constr:(NSStart b nse1)
        | _ =>
            let n := lookup e emap in
            constr:(NSMeta (@nil (string * nsval)) n)
        end
      with reifyVal v :=
        lazymatch v with
        | LitV ?b =>
            constr:(NSLitV b)
        | _ =>
            let n := lookup v vmap in
            constr:(NSMetaV  n)
        end
      in reifyExpr e0.

    Section ReifyTest.
      Axiom P : expr -> Prop.

      Ltac reifyTest :=
        match goal with
        | |- P ?e =>
            mkMapExpr (@nil expr) (@nil val) e
              ltac:(fun emap vmap =>
                      idtac "reify.cont.before" emap vmap e;
                      let e' := reifyExpr emap vmap e in
                      idtac "reify.cont.after" emap vmap e';
                      change (P (ndenote emap vmap e')))
        end.


      Goal P (Val #()).
      Proof. reifyTest. simpl. Abort.

    End ReifyTest.

    Ltac nsreify :=
      match goal with
      |- environments.envs_entails ?E (aneris_wp ?ip ?m ?e ?Φ) =>
          mkMapExpr (@nil expr) (@nil val) e
            ltac:(fun emap vmap =>
                    let e' := reifyExpr emap vmap e in
                    change (environments.envs_entails E
                              (aneris_wp ip m (ndenote emap vmap e') Φ)))
      end.

    Ltac nswp_pures :=
      nsreify;
      simple apply nsymbolic_reduce_wp_sound;
      simpl.

    Ltac nswp_pures' :=
      nsreify;
      (* eapply because of e' *)
      simple eapply reduce_sound;
      [ (* reduce = .. *)
        vm_compute; reflexivity
      | (* envs_entails  *)
        simpl
      ].

  Lemma runner_spec :
    {{{ inv paxosN paxos_inv ∗
        ([∗ set] a ∈ acceptors, a ⤇ acceptor_si) ∗
        ([∗ set] p ∈ proposers, p ⤇ proposer_si) ∗
        ([∗ set] l ∈ learners, l ⤇ learner_si) ∗
        c_addr ⤇ client_si ∗
        ([∗ set] l ∈ learners, l ⤳ (∅, ∅)) ∗
        c_addr ⤳ (∅, ∅) ∗
        ([∗ set] ip ∈ ips, free_ip ip) ∗
        ([∗ set] a ∈ acceptors, ∃ prf, maxBal_frag (a ↾ prf) None ∗
                                    maxVal_frag (a ↾ prf) None) ∗
        pending_class 0 0 ∗ pending_class 1 0 }}}
        runner 41 42 @["system"]
    {{{ v, RET v; True }}}.
  Proof.
    iIntros (Φ) "(#Hinv & #Has_si & #Hps_si & #Hls_si & #Hc_si &
                  Hls & Hch & Hips & Hfrags & Hpend0 & Hpend1) HΦ".
    rewrite /runner.
    do 8 (wp_makeaddress; wp_let). (* ~1.6s *)
    (* nsreify. *)
    (* simple eapply reduce_sound. *)
    (* vm_compute. *)
    (* reflexivity. *)
    (* simpl. *)
    (* Time swp_pures.  (* 0.27-0.29s *) *)
    (* Time nswp_pures. (* 0.23-0.26s *) *)
    (* Time nswp_pures'. (* 0.013 - 0.016s *) *)
    wp_apply (wp_set_empty socket_address); [done|]; iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (? Has).
    rewrite union_empty_r_L union_assoc_L in Has.
    wp_let.
    wp_apply (wp_set_empty socket_address); [done|]; iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (? Hls).
    rewrite union_empty_r_L in Hls.
    wp_let.
    iDestruct (big_sepS_delete _ _ "p1" with "Hips") as "(Hp1 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "p2" with "Hips") as "(Hp2 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "a1" with "Hips") as "(Ha1 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "a2" with "Hips") as "(Ha2 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "a3" with "Hips") as "(Ha3 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "l1" with "Hips") as "(Hl1 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "l2" with "Hips") as "(Hl2 & Hips)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ "c" with "Hips") as "(Hc & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l1_addr with "Hls") as "(Hl1h & Hls)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l2_addr with "Hls") as "(Hl2h & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a1_addr with "Has_si") as "(Ha1_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a2_addr with "Has_si") as "(Ha2_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a3_addr with "Has_si") as "(Ha3_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ p1_addr with "Hps_si") as "(Hp1_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ p2_addr with "Hps_si") as "(Hp2_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l1_addr with "Hls_si") as "(Hl1_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ l2_addr with "Hls_si") as "(Hl2_si & _)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a1_addr with "Hfrags") as "((% & Ha1_frag1 & Ha1_frag2) & Hfrags)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a2_addr with "Hfrags") as "((% & Ha2_frag1 & Ha2_frag2) & Hfrags)"; [set_solver|].
    iDestruct (big_sepS_delete _ _ a3_addr with "Hfrags") as "((% & Ha3_frag1 & Ha3_frag2) & _)"; [set_solver|].
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Ha1".
    iSplitR "Ha1_frag1 Ha1_frag2"; last first.
    { iIntros "!> Hport".
      wp_apply (acceptor_spec (_ ↾ _) with "Hinv Hls_si Hps_si Ha1_si Hport Ha1_frag1 Ha1_frag2");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Ha2".
    iSplitR "Ha2_frag1 Ha2_frag2"; last first.
    { iIntros "!> Hport".
      wp_apply (acceptor_spec (_ ↾ _) with "Hinv Hls_si Hps_si Ha2_si Hport Ha2_frag1 Ha2_frag2");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Ha3".
    iSplitR "Ha3_frag1 Ha3_frag2"; last first.
    { iIntros "!> Hport".
      wp_apply (acceptor_spec (_ ↾ _) with "Hinv Hls_si Hps_si Ha3_si Hport Ha3_frag1 Ha3_frag2");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hl1".
    iSplitR "Hl1h"; last first.
    { iIntros "!> Hport".
      assert (l1_addr ∈ Learners) as Hin by set_solver.
      iPoseProof (mapsto_messages_pers_alloc _ learner_si with "Hl1h []") as "Hl1h"; [done|].
      wp_apply (learner'_spec (l1_addr ↾ Hin) with "Hl1_si Hc_si Hport Hl1h");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hl2".
    iSplitR "Hl2h"; last first.
    { iIntros "!> Hport".
      assert (l2_addr ∈ Learners) as Hin by set_solver.
      iPoseProof (mapsto_messages_pers_alloc _ learner_si with "Hl2h []") as "Hl2h"; [done|].
      wp_apply (learner'_spec (l2_addr ↾ Hin) with "Hl2_si Hc_si Hport Hl2h");
        [done|..]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hp1".
    iSplitR "Hpend0"; last first.
    { iIntros "!> Hport".
      assert (p1_addr ∈ Proposers) as Hin by set_solver.
      assert (41%Z ∈ values) as H41 by set_solver.
      wp_apply (proposer'_spec _ _ (p1_addr ↾ Hin) (41%Z ↾ H41)
                  with "Hinv Has_si Hport Hp1_si Hpend0");
        [|done].
      rewrite ?size_union ?size_singleton; [lia|set_solver]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hp2".
    iSplitR "Hpend1"; last first.
    { iIntros "!> Hport".
      assert (p2_addr ∈ Proposers) as Hin by set_solver.
      assert (42%Z ∈ values) as H42 by set_solver.
      wp_apply (proposer'_spec _ _ (p2_addr ↾ Hin) (42%Z ↾ H42)
                  with "Hinv Has_si Hport Hp2_si Hpend1");
        [|done].
      rewrite ?size_union ?size_singleton; [lia|set_solver]. }
    iModIntro. wp_seq.
    wp_apply (aneris_wp_start {[80]}%positive). iFrame "Hc".
    iSplitR "Hch"; last first.
    { iIntros "!> Hport".
      iPoseProof (mapsto_messages_pers_alloc _ client_si with "Hch []") as "Hch"; [done|].
      wp_apply aneris_wp_wand_r.
      iSplitL; [wp_apply (client_spec with "Hinv Hc_si Hport Hch"); set_solver|].
      eauto. }
    by iApply "HΦ".
  Time Qed.
  (* do 8 wp_let 2.8 - 3.0s *)
  (* swp_pures 2.15 - 2.35s *)
  (* nswp_pures: 2.1 - 2.3s *)
  (* nswp_pures': 2.1 - 2.25 *)

  End NewSymbolic.

End runner.
