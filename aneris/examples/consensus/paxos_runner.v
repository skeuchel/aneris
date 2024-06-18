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

Inductive nsexpr : Set :=
| NSMeta : list (string * nsval) → nat → nsexpr
| NSVal : nsval → nsexpr
| NSVar : string → nsexpr
| NSRec : binder → binder → nsexpr → nsexpr
| NSApp : nsexpr → nsexpr → nsexpr
| NSUnOp : un_op → nsexpr → nsexpr
| NSBinOp : bin_op → nsexpr → nsexpr → nsexpr
| NSIf : nsexpr → nsexpr → nsexpr → nsexpr
| NSFindFrom : nsexpr → nsexpr → nsexpr → nsexpr
| NSSubstring : nsexpr → nsexpr → nsexpr → nsexpr
| NSRand : nsexpr → nsexpr
| NSPair : nsexpr → nsexpr → nsexpr
| NSFst : nsexpr → nsexpr
| NSSnd : nsexpr → nsexpr
| NSInjL : nsexpr → nsexpr
| NSInjR : nsexpr → nsexpr
| NSCase : nsexpr → nsexpr → nsexpr → nsexpr
| NSFork : nsexpr → nsexpr
| NSAlloc : option string → nsexpr → nsexpr
| NSLoad : nsexpr → nsexpr
| NSStore : nsexpr → nsexpr → nsexpr
| NSCAS : nsexpr → nsexpr → nsexpr → nsexpr
| NSMakeAddress : nsexpr → nsexpr → nsexpr
| NSGetAddressInfo : nsexpr → nsexpr
| NSNewSocket : nsexpr → nsexpr
| NSSocketBind : nsexpr → nsexpr → nsexpr
| NSSendTo : nsexpr → nsexpr → nsexpr → nsexpr
| NSReceiveFrom : nsexpr → nsexpr
| NSSetReceiveTimeout : nsexpr → nsexpr → nsexpr → nsexpr
| NSStart : base_lit → nsexpr → nsexpr
| NSSetEmpty : nsexpr
| NSSetAdd : nsexpr → nsexpr → nsexpr
with nsval : Set :=
| NSMetaV : nat -> nsval
  (* HACK: Use HOAS for binders introduced during execution. Replace by a *)
  (* first order representation. *)
| NSHoasV : val -> nsval
| NSLitV : base_lit → nsval
| NSRecV : binder → binder → nsexpr → nsval
| NSPairV : nsval → nsval → nsval
| NSInjLV : nsval → nsval
| NSInjRV : nsval → nsval
| NSSetEmptyV : nsval
| NSSetAddV : nsval.

Inductive nsset : Set :=
| nsempty.

Inductive NSProp :=
| NSIsSet : nsset → nsval → NSProp.

Inductive NSFree (A : Type) :=
| NSPure (a : A)
| NSForall (k : val → NSFree A)
| NSAssume (F : NSProp) (k : NSFree A)
| NSAssert (F : NSProp) (k : NSFree A)
| NSLater (k : NSFree A).

Notation NSLam x e := (NSRec BAnon x e) (only parsing).
Notation NSLet x e1 e2 := (NSApp (NSLam x e2) e1) (only parsing).
Notation NSSeq e1 e2 := (NSLet BAnon e1 e2) (only parsing).
Notation NSMatch e0 x1 e1 x2 e2 := (NSCase e0 (NSLam x1 e1) (NSLam x2 e2)) (only parsing).

Notation NSubst := (list (string * nsval)).
Notation Subst := (list (string * val)).

Section Denote.

  Fixpoint substs (s : Subst) (e : expr) {struct s} : expr :=
    match s with
    | nil => e
    | cons (x,v) s' => subst' x v (substs s' e)
    end.

  Variant meta :=
  | meta_expr (e : expr)
  | meta_val  (v : val).

  Context (mmap : list meta).

  Definition ndenote_subst (ndenote_val : nsval -> val) : NSubst -> Subst :=
    fix ndenote_subst (s : NSubst) {struct s} : Subst :=
      match s with
      | nil => nil
      | cons (x, v) s' => cons (x, ndenote_val v) (ndenote_subst s')
      end.

  Fixpoint ndenote_expr(e : nsexpr) : expr :=
    match e with
    | NSMeta s n => match nth_error mmap n with
                    | Some (meta_expr e1) => substs (ndenote_subst ndenote_val s) e1
                    | _                   => #()
                    end
    | NSVal v => Val (ndenote_val v)
    | NSVar x => Var x
    | NSRec f x e1 => Rec f x (ndenote_expr e1)
    | NSApp e1 e2 => App (ndenote_expr e1) (ndenote_expr e2)
    | NSUnOp op e1 => UnOp op (ndenote_expr e1)
    | NSBinOp op e1 e2 => BinOp op (ndenote_expr e1) (ndenote_expr e2)
    | NSIf e1 e2 e3 => If (ndenote_expr e1) (ndenote_expr e2) (ndenote_expr e3)
    | NSFindFrom e1 e2 e3 => FindFrom (ndenote_expr e1) (ndenote_expr e2) (ndenote_expr e3)
    | NSSubstring e1 e2 e3 => Substring (ndenote_expr e1) (ndenote_expr e2) (ndenote_expr e3)
    | NSRand e1 => Rand (ndenote_expr e1)
    | NSPair e1 e2 => Pair (ndenote_expr e1) (ndenote_expr e2)
    | NSFst e1 => Fst (ndenote_expr e1)
    | NSSnd e1 => Snd (ndenote_expr e1)
    | NSInjL e1 => InjL (ndenote_expr e1)
    | NSInjR e1 => InjR (ndenote_expr e1)
    | NSCase e1 e2 e3 => Case (ndenote_expr e1) (ndenote_expr e2) (ndenote_expr e3)
    | NSFork e1 => Fork (ndenote_expr e1)
    | NSAlloc s e1 => Alloc s (ndenote_expr e1)
    | NSLoad e1 => Load (ndenote_expr e1)
    | NSStore e1 e2 => Store (ndenote_expr e1) (ndenote_expr e2)
    | NSCAS e1 e2 e3 => CAS (ndenote_expr e1) (ndenote_expr e2) (ndenote_expr e3)
    | NSMakeAddress e1 e2 => MakeAddress (ndenote_expr e1) (ndenote_expr e2)
    | NSGetAddressInfo e1 => GetAddressInfo (ndenote_expr e1)
    | NSNewSocket e1 => NewSocket (ndenote_expr e1)
    | NSSocketBind e1 e2 => SocketBind (ndenote_expr e1) (ndenote_expr e2)
    | NSSendTo e1 e2 e3 => SendTo (ndenote_expr e1) (ndenote_expr e2) (ndenote_expr e3)
    | NSReceiveFrom e1 => ReceiveFrom (ndenote_expr e1)
    | NSSetReceiveTimeout e1 e2 e3 => SetReceiveTimeout (ndenote_expr e1) (ndenote_expr e2) (ndenote_expr e3)
    | NSStart b e1 => Start b (ndenote_expr e1)
    | NSSetEmpty => set_empty #()
    | NSSetAdd e1 e2 => set_add (ndenote_expr e1) (ndenote_expr e2)
    end
  with
  ndenote_val (v : nsval) : val :=
    match v with
    | NSMetaV n => match nth_error mmap n with
                   | Some (meta_val v1) => v1
                   | _                  => #()
                   end
    | NSHoasV v => v
    | NSLitV v1 => LitV v1
    | NSRecV f x e => RecV f x (ndenote_expr e)
    | NSPairV v1 v2 => PairV (ndenote_val v1) (ndenote_val v2)
    | NSInjLV v1 => InjLV (ndenote_val v1)
    | NSInjRV v1 => InjRV (ndenote_val v1)
    | NSSetEmptyV => set_empty
    | NSSetAddV => set_add
    end.

  Definition ndenotes (o : option (nsexpr + nsval)) : option (expr + val) :=
    match o with
    | Some (inl nse) => Some (inl (ndenote_expr nse))
    | Some (inr nsv) => Some (inr (ndenote_val nsv))
    | None           => None
    end.

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
    | NSUnOp op e1 => NSUnOp op (nssubst x v e1)
    | NSBinOp op e1 e2 => NSBinOp op (nssubst x v e1) (nssubst x v e2)
    | NSIf e1 e2 e3 => NSIf (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
    | NSFindFrom e1 e2 e3 => NSFindFrom (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
    | NSSubstring e1 e2 e3 => NSSubstring (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
    | NSRand e1 => NSRand (nssubst x v e1)
    | NSPair e1 e2 => NSPair (nssubst x v e1) (nssubst x v e2)
    | NSFst e => NSFst (nssubst x v e)
    | NSSnd e => NSSnd (nssubst x v e)
    | NSInjL e => NSInjL (nssubst x v e)
    | NSInjR e => NSInjR (nssubst x v e)
    | NSCase e1 e2 e3 => NSCase (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
    | NSFork e1 => NSFork (nssubst x v e1)
    | NSAlloc s e1 => NSAlloc s (nssubst x v e1)
    | NSLoad e => NSLoad (nssubst x v e)
    | NSStore e1 e2 => NSStore (nssubst x v e1) (nssubst x v e2)
    | NSCAS e1 e2 e3 => NSCAS (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
    | NSMakeAddress e1 e2 => NSMakeAddress (nssubst x v e1) (nssubst x v e2)
    | NSGetAddressInfo e1 => NSGetAddressInfo (nssubst x v e1)
    | NSNewSocket e1 => NSNewSocket (nssubst x v e1)
    | NSSocketBind e1 e2 => NSSocketBind (nssubst x v e1) (nssubst x v e2)
    | NSSendTo e1 e2 e3 => NSSendTo (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
    | NSReceiveFrom e1 => NSReceiveFrom (nssubst x v e1)
    | NSSetReceiveTimeout e1 e2 e3 => NSSetReceiveTimeout (nssubst x v e1) (nssubst x v e2) (nssubst x v e3)
    | NSStart b e1 => NSStart b (nssubst x v e1)
    | NSSetEmpty => NSSetEmpty
    | NSSetAdd e1 e2 => NSSetAdd (nssubst x v e1) (nssubst x v e2)
    end.

  Definition nssubst' (mx : binder) (v : nsval) : nsexpr → nsexpr :=
    match mx with
    | BAnon => id
    | BNamed x => nssubst x v
    end.

  Definition ndenote_set (s : nsset) : gset socket_address :=
    match s with
    | nsempty => ∅
    end.

  Definition ndenote_formula (F : NSProp) : Prop :=
    match F with
    | NSIsSet n n0 => is_set (ndenote_set n) (ndenote_val n0)
    end.

  Fixpoint ndenote_free {R} (m : NSFree R) (Φ : R -> Prop) {struct m} : Prop :=
    match m with
    | NSPure _ a => Φ a
    | NSForall _ k => ∀ v : val, ndenote_free (k v) Φ
    | NSAssume _ F k => ndenote_formula F → ndenote_free k Φ
    | NSAssert _ F k => ndenote_formula F ∧ ndenote_free k Φ
    | NSLater _ k => ndenote_free k Φ
    end.

End Denote.
#[global] Arguments ndenote_expr _ _ /.
#[global] Arguments ndenote_val _ _ /.
#[global] Arguments ndenotes _ _ /.

    Fixpoint reduce_free_aux {R} (n : nat) :
      nsexpr → (nsexpr → NSFree R) → (nsval → NSFree R) → NSFree R :=
      match n with
      | O   => fun e Ψ Φ => Ψ e
      | S n => fix go (e : nsexpr) (Ψ : nsexpr → NSFree R)
                 (Φ : nsval → NSFree R) {struct e} : NSFree R :=
        match e with
        | NSMeta s n => Ψ (NSMeta s n)
        | NSVal v => Φ v
        | NSPair e1 e2 =>
            go e2
              (fun e2' => Ψ (NSPair e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (NSPair e1' (NSVal v2)))
                   (fun v1  => Φ (NSPairV v1 v2)))
        | NSApp e1 e2 =>
            go e2
              (fun e2' => Ψ (NSApp e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (NSApp e1' (NSVal v2)))
                   (fun v1 =>
                      match v1 with
                      | NSRecV f x e3 =>
                          NSLater _ (reduce_free_aux n
                                    (nssubst' x v2 (nssubst' f (NSRecV f x e3) e3)) Ψ Φ)
                      | _ => Ψ (NSApp (NSVal v1) (NSVal v2))
                      end))
        | NSStore e1 e2 =>
            go e2
              (fun e2' => Ψ (NSStore e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (NSStore e1' (NSVal v2)))
                   (fun v1  => Ψ (NSStore (NSVal v1) (NSVal v2))))
        | NSBinOp op e1 e2 =>
            go e2
              (fun e2' => Ψ (NSBinOp op e1 e2'))
              (fun v2 =>
                 go e1
                   (fun e1' => Ψ (NSBinOp op e1' (NSVal v2)))
                   (fun v1 =>
                      (* TODO: The concrete reduction of values requires plugging *)
                      (*                  *)
                      (* match bin_op_eval op (ndenote_val v1) (ndenote_val v2) with *)
                      (* | Some v => Φ (NSMetaV v) (S nsteps) *)
                      (* | None => Ψ (NSBinOp op (NSVal v1) (NSVal v2)) nsteps *)
                      (* end *)
                      Ψ (NSBinOp op (NSVal v1) (NSVal v2))))
        | NSMatch e0 x1 e1 x2 e2 =>
            go e0
              (fun e0' => Ψ (NSMatch e0' x1 e1 x2 e2))
              (fun v0 =>
                 match v0 with
                 | NSInjLV v => NSLater _ (reduce_free_aux n (nssubst' x1 v e1) Ψ Φ)
                 | NSInjRV v => NSLater _ (reduce_free_aux n (nssubst' x2 v e2) Ψ Φ)
                 | _         => Ψ (NSMatch (NSVal v0) x1 e1 x2 e2)
                 end)
        | NSSnd (NSVal (NSPairV v1 v2)) => NSLater _ (Φ v2)
        | NSRec f x e => NSLater _ (Φ (NSRecV f x e))
        | NSMakeAddress (NSVal (NSLitV (LitString s))) (NSVal (NSLitV (LitInt p))) =>
            NSLater _ (Φ (NSLitV (LitSocketAddress (SocketAddressInet s (Z.to_pos p)))))
        | NSSetEmpty => NSLater _ (NSForall _ (fun v => NSAssume _ (NSIsSet nsempty (NSHoasV v)) (Φ (NSHoasV v))))
        (* | NSSetAdd e1 e2 => *)
        (*     go e2 *)
        (*       (fun e2' => Ψ (NSSetAdd e1 e2')) *)
        (*       (fun v2 => *)
        (*          go e1 *)
        (*            (fun e1' => Ψ (NSSetAdd e1' (NSVal v2))) *)
        (*            (fun v1 => *)
        (*               NSAssert (NSIsSet *)
        (*               Ψ (NSSetAdd (NSVal v1) (NSVal v2))))) *)
        (*               (* match v1 with *) *)
        (*               (* | NSRecV f x e3 => *) *)
        (*               (*     NSLater _ (reduce_free_aux n *) *)
        (*               (*                 (nssubst' x v2 (nssubst' f (NSRecV f x e3) e3)) Ψ Φ) *) *)
        (*               (* | _ => Ψ (NSApp (NSVal v1) (NSVal v2)) *) *)
        (*               (* end)) *) *)

        | _ => Ψ e
        end
      end.

    Definition reduce_free (e : nsexpr) : NSFree (nsexpr + nsval) :=
      reduce_free_aux 10 e (fun e => NSPure _ (inl e)) (fun v => NSPure _ (inr v)).
    #[global] Arguments reduce_free e /.

    Lemma tac_wp_reduce_free_sound (Δ : environments.envs (iPropI Σ)) E
      (ip : ip_address) (mmap : list meta) (e : nsexpr) (Φ : val → iProp Σ) :
      forall m,
      reduce_free e = m ->
      ndenote_free mmap m
        (fun ev =>
           match ev with
           | inl e => environments.envs_entails Δ (aneris_wp ip E (ndenote_expr mmap e) Φ)
           | inr v => environments.envs_entails Δ (▷ Φ (ndenote_val mmap v))
           end) →
      environments.envs_entails Δ (aneris_wp ip E (ndenote_expr mmap e) Φ).
    Proof. Admitted.

    Ltac tac_wp_in_list x xs :=
      match xs with
      | @nil _         => false
      | @cons _ x _    => true
      | @cons _ _ ?xs' => tac_wp_in_list x xs'
      end.

    Ltac tac_wp_add_to_mmap m mmap :=
      let b := tac_wp_in_list m mmap in
      match b with
      | true => mmap
      | false => constr:(@cons meta m mmap)
      end.

Ltac tac_wp_mk_map_expr
  mmap0 (* : list meta *)
  e0    (* : expr *)
  tac0  (* : list meta -> r *)
        (* : r *)
  :=
  let rec tac_wp_mk_map_expr mmap e tac :=
    (* idtac "tac_wp_mk_map_expr" mmap e; *)
    lazymatch e with
    | Val ?v =>
        tac_wp_mk_map_val mmap v tac
    | Var ?x =>
        (* TODO: We do not allow meta-variables inside strings,
           so should we check if x is ground? *)
        tac mmap
    | Rec ?b1 ?b2 ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | App ?e1 ?e2 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 tac)
    | UnOp ?op ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | BinOp ?op ?e1 ?e2 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 tac)
    | If ?e1 ?e2 ?e3 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 ltac:(fun mmap2 =>
        tac_wp_mk_map_expr mmap2 e3 tac))
    | FindFrom ?e1 ?e2 ?e3 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 ltac:(fun mmap2 =>
        tac_wp_mk_map_expr mmap2 e3 tac))
    | Substring ?e1 ?e2 ?e3 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 ltac:(fun mmap2 =>
        tac_wp_mk_map_expr mmap2 e3 tac))
    | Rand ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | Pair ?e1 ?e2 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 tac)
    | Fst ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | Snd ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | InjL ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | InjR ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | Case ?e1 ?e2 ?e3 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 ltac:(fun mmap2 =>
        tac_wp_mk_map_expr mmap2 e3 tac))
    | Alloc ?s ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | MakeAddress ?e1 ?e2 =>
        tac_wp_mk_map_expr mmap e1 ltac:(fun mmap1 =>
        tac_wp_mk_map_expr mmap1 e2 tac)
    | Start ?b ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | _      =>
        (* idtac "tac_wp_mk_map_expr.default.beforeAddToMap" mmap; *)
        let mmap' := tac_wp_add_to_mmap constr:(meta_expr e) mmap in
        (* idtac "tac_wp_mk_map_expr.default.afterAddToMap" mmap'; *)
        tac mmap'
    end
  with tac_wp_mk_map_val mmap v tac :=
    lazymatch v with
    | LitV ?b =>
        (* TODO: We do not allow meta-variables inside base_lits,
           so should we check if b is ground? *)
        tac mmap
    | RecV ?b1 ?b2 ?e1 =>
        tac_wp_mk_map_expr mmap e1 tac
    | PairV ?v1 ?v2 =>
        tac_wp_mk_map_val mmap v1 ltac:(fun mmap1 =>
        tac_wp_mk_map_val mmap1 v2 tac)
    | InjLV ?v1 =>
        tac_wp_mk_map_val mmap v1 tac
    | InjRV ?v1 =>
        tac_wp_mk_map_val mmap v1 tac
    | set_empty =>
        tac mmap
    | set_add =>
        tac mmap
    | _ =>
        let mmap' := tac_wp_add_to_mmap constr:(meta_val v) mmap in
        tac mmap'
    end
  in tac_wp_mk_map_expr mmap0 e0 tac0.

Ltac tac_wp_map_lookup
  (* forall a. *)
  x  (* : a *)
  xs (* : list a *)
     (* : nat *)
  := lazymatch xs with
     | @cons _ x _    => O
     | @cons _ _ ?xs' =>
         let n := tac_wp_map_lookup x xs' in
         constr:(S n)
     end.

Ltac tac_wp_reify_expr mmap e0 :=
  let rec tac_wp_reify_expr e :=
    lazymatch e with
    | App (Val set_empty) (Val (LitV LitUnit)) =>
        constr:(NSSetEmpty)
    | Val ?v =>
        let nsv := tac_wp_reify_val v in
        constr:(NSVal nsv)
    | Var ?x =>
        constr:(NSVar x)
    | Rec ?b1 ?b2 ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSRec b1 b2 nse1)
    | App ?e1 ?e2 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        constr:(NSApp nse1 nse2)
    | UnOp ?op ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSUnOp op nse1)
    | BinOp ?op ?e1 ?e2 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        constr:(NSBinOp op nse1 nse2)
    | If ?e1 ?e2 ?e3 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        let nse3 := tac_wp_reify_expr e3 in
        constr:(NSIf nse1 nse2 nse3)
    | FindFrom ?e1 ?e2 ?e3 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        let nse3 := tac_wp_reify_expr e3 in
        constr:(NSFindFrom nse1 nse2 nse3)
    | Substring ?e1 ?e2 ?e3 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        let nse3 := tac_wp_reify_expr e3 in
        constr:(NSSubstring nse1 nse2 nse3)
    | Rand ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSRand op nse1)
    | Pair ?e1 ?e2 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        constr:(NSPair nse1 nse2)
    | Fst ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSFst nse1)
    | Snd ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSSnd nse1)
    | InjL ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSInjL nse1)
    | InjR ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSInjR nse1)
    | Case ?e1 ?e2 ?e3 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        let nse3 := tac_wp_reify_expr e3 in
        constr:(NSCase nse1 nse2 nse3)
    | Alloc ?s ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSAlloc s nse1)
    | MakeAddress ?e1 ?e2 =>
        let nse1 := tac_wp_reify_expr e1 in
        let nse2 := tac_wp_reify_expr e2 in
        constr:(NSMakeAddress nse1 nse2)
    | Start ?b ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSStart b nse1)
    | _ =>
        let n := tac_wp_map_lookup constr:(meta_expr e) mmap in
        constr:(NSMeta (@nil (string * nsval)) n)
    end
  with tac_wp_reify_val v :=
    lazymatch v with
    | LitV ?b =>
        constr:(NSLitV b)
    | RecV ?b1 ?b2 ?e1 =>
        let nse1 := tac_wp_reify_expr e1 in
        constr:(NSRecV b1 b2 nse1)
    | PairV ?v1 ?v2 =>
        let nsv1 := tac_wp_reify_val v1 in
        let nsv2 := tac_wp_reify_val v2 in
        constr:(NSPairV nsv1 nsv2)
    | InjLV ?v1 =>
        let nsv1 := tac_wp_reify_val v1 in
        constr:(NSInjLV nsv1)
    | InjRV ?v1 =>
        let nsv1 := tac_wp_reify_val v1 in
        constr:(NSInjRV nsv1)
    | set_empty =>
        constr:(NSSetEmptyV)
    | set_add =>
        constr:(NSSetAddV)
    | _ =>
        let n := tac_wp_map_lookup constr:(meta_val v) mmap in
        constr:(NSMetaV  n)
    end
  in tac_wp_reify_expr e0.

Ltac tac_wp_reify :=
  match goal with
  |- environments.envs_entails ?E (aneris_wp ?ip ?m ?e ?Φ) =>
      (* Simplify to reduce some calls to [inject] like [Inject_expr]. *)
      let e := eval simpl in e in
      tac_wp_mk_map_expr (@nil meta) e
        ltac:(fun mmap =>
                let e' := tac_wp_reify_expr mmap e in
                change (environments.envs_entails E
                          (aneris_wp ip m (ndenote_expr mmap e') Φ)))
  end.

Ltac wp_free_pures :=
  iStartProof;
  try
    (tac_wp_reify;
     (* eapply because of e' *)
     simple eapply tac_wp_reduce_free_sound;
     [ (* reduce = .. *)
       vm_compute; reflexivity
     | (* ndenote_free *)
       simpl
     ]).

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
    (* do 8 (wp_makeaddress; wp_let). (* ~1.6s *) *)
    (* nsreify. *)
    (* simple eapply reduce_sound. *)
    (* vm_compute. *)
    (* reflexivity. *)
    (* simpl. *)
    (* Time swp_pures.  (* 0.27-0.29s *) *)
    (* Time nswp_pures. (* 0.23-0.26s *) *)
    (* Time nswp_pures'. (* 0.013 - 0.016s *) *)

    Time wp_pures.
    Time wp_free_pures; intros ? ?.
    (* Time wp_apply (wp_set_empty socket_address); [done|]; iIntros (??). *)
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (??).
    wp_apply (wp_set_add with "[//]"); iIntros (? Has).
    rewrite union_empty_r_L union_assoc_L in Has.
    wp_let.
    Time wp_free_pures; intros ? ?.
    (* Time wp_apply (wp_set_empty socket_address); [done|]; iIntros (??). *)
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

End runner.
