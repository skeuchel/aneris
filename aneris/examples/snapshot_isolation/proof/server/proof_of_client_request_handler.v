(* From iris.algebra Require Import auth gmap dfrac frac_auth excl csum. *)
(* From iris.algebra.lib Require Import mono_list dfrac_agree. *)
(* From iris.base_logic Require Import invariants. *)
(* From iris.bi.lib Require Import fractional. *)
(* From iris.proofmode Require Import tactics coq_tactics reduction spec_patterns. *)
(* From aneris.lib Require Import gen_heap_light. *)
(* From aneris.aneris_lang Require Import lang resources inject tactics proofmode. *)
(* From aneris.aneris_lang.lib Require Import list_proof lock_proof map_proof. *)
(* From aneris.aneris_lang.lib.serialization Require Import serialization_proof. *)
(* From aneris.aneris_lang.program_logic Require Import lightweight_atomic. *)
(* From aneris.aneris_lang.program_logic Require Import aneris_lifting. *)
(* From aneris.aneris_lang.program_logic Require Import aneris_weakestpre. *)
(* From aneris.examples.reliable_communication.lib.mt_server *)
(*      Require Import user_params mt_server_code. *)
(* From aneris.examples.reliable_communication.lib.mt_server.spec *)
(*      Require Import api_spec. *)
(* From aneris.examples.snapshot_isolation *)
(*      Require Import snapshot_isolation_code. *)
(* From aneris.examples.snapshot_isolation.specs *)
(*      Require Import user_params resources specs. *)
(* From aneris.examples.snapshot_isolation.proof *)
(*      Require Import time events model kvs_serialization rpc_user_params. *)
(* From aneris.examples.snapshot_isolation.proof.resources *)
(*      Require Import *)
(*      resource_algebras server_resources proxy_resources *)
(*      global_invariant local_invariant wrappers. *)
(* From aneris.examples.snapshot_isolation.instantiation *)
(*      Require Import snapshot_isolation_api_implementation. *)

(* Section Proof_of_handler. *)

(*   Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}. *)
(*   Context (clients : gset socket_address). *)
(*   Context (γKnownClients γGauth γGsnap γT γlk : gname). *)
(*   Context (srv_si : message → iProp Σ). *)
(*   Notation MTC := (client_handler_rpc_user_params *)
(*                      clients γKnownClients γGauth γGsnap γT). *)
(*   Import snapshot_isolation_code_api. *)

(*   Lemma client_request_handler_spec (lk : val) (kvs vnum : loc) : *)
(*     ∀ reqv reqd, *)
(*     {{{ server_lock_inv γGauth γT γlk lk kvs vnum ∗ *)
(*         MTC.(MTS_handler_pre) reqv reqd }}} *)
(*         client_request_handler lk #kvs #vnum reqv  @[ip_of_address MTC.(MTS_saddr)] *)
(*     {{{ repv repd, RET repv; *)
(*         ⌜Serializable (rep_serialization) repv⌝ ∗ *)
(*          MTC.(MTS_handler_post) repv reqd repd }}}. *)
(*   Proof. *)
(*     iIntros (reqv reqd Φ) "(#Hlk & Hpre) HΦ". *)
(*     rewrite /client_request_handler. *)
(*     wp_pures. *)
(*     rewrite /MTS_handler_pre //= /ReqPre. *)
(*     rewrite /lk_handle. *)
(*     iDestruct "Hpre" as "(#HGlobInv & [HpreRead|[HpreStart|HpreCommit]])". *)
(*     (* Proof of read request. *) *)
(*     1:{ admit. } *)
(*     (* Proof of commit request. *) *)
(*     2:{ admit. } *)
(*     iDestruct "HpreStart" *)
(*       as (E P Q Hreqd ->) "(%HinE & HP & Hsh)". *)
(*     wp_pures. *)
(*     wp_lam. *)
(*     rewrite /start_handler. *)
(*     wp_pures. *)
(*     wp_apply (acquire_spec with "[Hlk]"); first by iFrame "#". *)
(*     iIntros (?) "(-> & Hlock & Hlkres)". *)
(*     wp_pures. *)
(*     iDestruct "Hlkres" *)
(*       as (kvsV T m M Hmap Hvalid) *)
(*            "(HmemLoc & HtimeLoc & HkvsL & HvnumL)". *)
(*     wp_load. *)
(*     wp_pures. *)
(*     (* This is where the viewshift is happening. *) *)
(*     wp_bind (Store _ _). *)
(*     wp_apply (aneris_wp_atomic _ _ E). *)
(*     iMod ("Hsh" with "[$HP]") as (mu) "(Hkeys & Hpost)". *)
(*     iInv KVS_InvName *)
(*       as (Mg Tg gMg) ">(HmemGlob & HtimeGlob & Hccls & %Hdom & %HkvsValid)". *)
(*     (* Logical updates. *) *)
(*     rewrite /ownTimeGlobal /ownTimeLocal. *)
(*     iDestruct (mono_nat.mono_nat_auth_own_agree with "[$HtimeGlob][$HtimeLoc]") *)
(*       as "(%Hleq & ->)". *)
(*     iAssert (mono_nat.mono_nat_auth_own γT (1 / 2) T -∗ *)
(*              mono_nat.mono_nat_auth_own γT (1 / 2) T -∗ *)
(*              mono_nat.mono_nat_auth_own γT 1 T)%I as "Htime". *)
(*     { iIntros "H1 H2". *)
(*       by iSplitL "H1". } *)
(*     assert (kvs_valid M (T + 1)) as HkvsValidST. *)
(*     { admit. } *)
(*     assert (kvsl_valid m M (T + 1)) as HkvsLValidST. *)
(*     { admit. } *)
(*     iDestruct ("Htime" with "[$HtimeGlob][$HtimeLoc]") as "HtimeAuth". *)
(*     iMod (mono_nat.mono_nat_own_update (T + 1) with "HtimeAuth") *)
(*       as "((HtimeGlob & HtimeLoc) & #HtimeSnap)"; first by lia. *)
(*     iAssert (⌜M = Mg⌝%I) as "<-". *)
(*     { iDestruct "HmemGlob" as "(Hg1 & Hg2)". *)
(*       rewrite /ownMemAuthLocal /ownMemAuthGlobal. *)
(*       iApply (ghost_map.ghost_map_auth_agree γGauth (1/2)%Qp (1/2)%Qp M with "[$HmemLoc][$Hg1]"). } *)
(*     iSplitL "HtimeGlob HmemGlob Hccls". *)
(*     { iModIntro. iNext. iExists M, (T+1), gMg. *)
(*       by iFrame "#∗". } *)
(*     iModIntro. *)
(*     iModIntro. *)
(*     wp_store. *)
(*     iAssert (⌜∀ k, mu !!k = (((λ h : list write_event, to_hist h) <$> (filter (λ k, k.1 ∈ dom mu) M))) !! k⌝%I) *)
(*       as "%df". *)
(*     iIntros (k). *)
(*     rewrite /OwnMemKey_def. *)
(*     - destruct (mu !! k) eqn:Hk. *)
(*       iDestruct (big_sepM_lookup_acc _ mu k _ with "[$Hkeys]") as "(Hp & Hclose)"; first done. *)
(*       iDestruct "Hp" as (hw) "(Hp & %Heq)". *)
(*       iAssert (⌜M !! k = Some hw⌝%I) as "%Heqhw". *)
(*       { simplify_eq /=. eauto. done. *)
(*       admit. *)
(*       rewrite Heq. simplify_eq /=. *)
(*       -- assert ((filter (λ k0, k0.1 ∈ dom mu) M) !! k = Some hw) as Heq'. *)
(*           apply map_filter_lookup_Some_2. *)
(*           done. *)
(*           admit. *)
(*           assert (((λ h : list write_event, to_hist h) <$> *)
(*     filter (λ k0 : Key * list write_event, k0.1 ∈ dom mu) M) !! k = *)

(*    (filter (λ k0 : Key * list val, k0.1 ∈ dom mu) ((λ h : list write_event, to_hist h) <$> M)) !! k) as ->. *)
(*           symmetry. rewrite map_filter_fmap. done. *)
(*           simplify_eq /=. *)
(*           iPureIntro. *)
(*           symmetry. apply map_filter_lookup_Some_2. *)
(*           simplify_eq /=. *)
(*           rewrite lookup_fmap. *)
(*           simplify_eq /=. *)
(*           rewrite Heqhw. *)
(*           simpl. *)
(*  done. admit. *)
(*     -- admit. *)
(*     - *)
(*     iDestruct ("Hpost" $! (T+1)%nat ((filter (λ k, k.1 ∈ dom mu) M)) with "[][Hkeys]") as "HQ". *)
(*     iPureIntro. *)
(*     apply map_eq. done. *)
(*     admit. *)
(*     iMod "HQ". *)
(*     iModIntro. *)
(*     wp_pures. *)
(*     wp_smart_apply (release_spec with "[-HQ HΦ]"). *)
(*     iFrame "#∗". *)
(*     rewrite /lkResDef. *)
(*     iExists  kvsV, ((T+1)%nat), m, M. *)
(*     replace (Z.of_nat T + 1)%Z with (Z.of_nat (T + 1)) by lia. *)
(*     iFrame "#∗". *)
(*     by iSplit; first done. *)
(*     iIntros (? ->). *)
(*     wp_pures. *)
(*     iApply "HΦ". *)
(*     iSplit. *)
(*     -- admit. *)
(*     -- rewrite /ReqPost. *)
(*       iFrame "#". *)
(*       iRight. *)
(*       iLeft. *)
(*       iExists E, P, Q, (T+1), M. *)
(*       iFrame "#∗". *)
(*       iPureIntro. *)
(*       split_and!; eauto. *)
(*       replace (Z.of_nat T + 1)%Z with (Z.of_nat (T + 1)) by lia. *)
(*       done. *)
(*     (* Proof of commit request. *) *)
(*   Admitted. *)

(* End Proof_of_handler. *)
