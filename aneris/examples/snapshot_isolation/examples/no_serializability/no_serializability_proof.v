From aneris.aneris_lang Require Import network resources proofmode.
From aneris.aneris_lang.lib Require Import
     list_proof inject lock_proof.
From aneris.aneris_lang.lib.serialization
     Require Import serialization_proof.
From aneris.aneris_lang.program_logic Require Import lightweight_atomic.
From aneris.examples.snapshot_isolation.specs
     Require Import user_params resources specs.
From aneris.aneris_lang Require Import tactics proofmode adequacy.
From trillium.prelude Require Import finitary.
From aneris.aneris_lang.program_logic Require Import
     aneris_weakestpre aneris_adequacy aneris_lifting.
From iris.base_logic.lib Require Import invariants.
From aneris.examples.snapshot_isolation.examples.no_serializability
      Require Import no_serializability_code.
Import ser_inj.
From aneris.examples.snapshot_isolation.instantiation
     Require Import snapshot_isolation_api_implementation.
From aneris.examples.snapshot_isolation.util Require Import util_proof.

Definition server_addr := SocketAddressInet "0.0.0.0" 80.
Definition client_1_addr := SocketAddressInet "0.0.0.1" 80.
Definition client_2_addr := SocketAddressInet "0.0.0.2" 80.
Definition client_3_addr := SocketAddressInet "0.0.0.3" 80.
Definition client_4_addr := SocketAddressInet "0.0.0.4" 80.

Instance params : User_params :=
{| KVS_address := server_addr;
  KVS_keys := {["x"; "y"; "z"]};
  KVS_InvName := nroot .@ "siinv";
  KVS_serialization := int_serialization;
  KVS_ser_inj := int_ser_is_ser_injective;
  KVS_ser_inj_alt := int_ser_is_ser_injective_alt
|}.

Definition client_inv_name := nroot.@"clinv".

Section proofs.

Context `{!anerisG Mdl Σ, !SI_resources Mdl Σ, !SI_client_toolbox}.

  Definition client_inv_def : iProp Σ :=
  ∃ hx hy hz, "x" ↦ₖ hx ∗ "y" ↦ₖ hy ∗ "z" ↦ₖ hz ∗
    ((⌜hx = []⌝ ∗ ⌜hy = []⌝ ∗ ⌜hz = []⌝) ∨
      (⌜#1 ∈ hz⌝ ∗ ∃ vx vy, ⌜hist_val hx = Some vx⌝ ∗ ⌜hist_val hy = Some vy⌝ ∗
      (⌜vx = #1⌝ ∨ ⌜vx = #(-1)⌝) ∗(⌜vy = #1⌝ ∨ ⌜vy = #(-1)⌝))).

  Definition client_inv : iProp Σ :=
    inv client_inv_name client_inv_def.

  Lemma transaction1_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction1 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ !>CanStart HΦ".
    rewrite/transaction1.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name));
      first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & init)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy; "z" := hz ]}.
    iFrame.
    iSplitL "x_hx y_hy z_hz";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & _)".
    iMod ("close" with "[mem init]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      repeat (iPoseProof (big_sepM_insert with "mem") as "(k_hk & mem)";
                first done; iFrame).
    }
    iModIntro.
    wp_pures.
    iPoseProof (big_sepM_insert with "cache") as "((x_hx & x_upd) & cache)";
      first done.
    iPoseProof (big_sepM_insert with "cache") as "((y_hy & y_upd) & cache)";
      first done.
    iPoseProof (big_sepM_insert with "cache") as "((z_hz & z_upd) & _)";
      first done.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$x_hx $x_upd]");
      first set_solver.
    iIntros "(x_1 & x_upd)".
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$y_hy $y_upd]");
      first set_solver.
    iIntros "(y_1 & y_upd)".
    wp_pures.
    wp_apply (SI_write_spec $! _ _ _ _ (SerVal #1) with "[] [$z_hz $z_upd]");
      first set_solver.
    iIntros "(z_1 & z_upd)".
    wp_pures.
    wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' & #init)" "close".
    iModIntro.
    iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, _,
      {[ "x" := (Some #1, true); "y" := (Some #1, true); "z" := (Some #1, true) ]}.
    iFrame.
    iSplitL "x_1 y_1 z_1 x_hx' y_hy' z_hz' x_upd y_upd z_upd".
    {
      rewrite !dom_insert_L !dom_empty_L.
      do 2 (iSplit; first done).
      by iSplitL "x_hx' y_hy' z_hz'";
        repeat (iApply big_sepM_insert; first done; iFrame).
    }
    have x_key : "x" ∈ KVS_keys by set_solver.
    have y_key : "y" ∈ KVS_keys by set_solver.
    have z_key : "z" ∈ KVS_keys by set_solver.
    iIntros "!>(CanStart & [(%can_commit & mem)|(_ & mem)])";
      (iMod ("close" with "[mem]") as "_"; last by iApply "HΦ").
    {
      iPoseProof (big_sepM2_insert with "mem") as "((x_1 & _) & mem)"; [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((y_1 & _) & mem)"; [done..|].
      iPoseProof (big_sepM2_insert with "mem") as "((z_1 & _) & _)"; [done..|].
      rewrite bool_decide_spec in can_commit.
      move: (can_commit _ x_key).
      rewrite lookup_insert bool_decide_spec !lookup_insert=>[][->].
      move: (can_commit _ y_key).
      rewrite lookup_insert_ne// lookup_insert bool_decide_spec lookup_insert_ne//
          lookup_insert lookup_insert_ne// lookup_insert=>[][->].
      move: (can_commit _ z_key).
      rewrite lookup_insert_ne// lookup_insert_ne// lookup_insert bool_decide_spec
            lookup_insert_ne// lookup_insert_ne// lookup_insert
            lookup_insert_ne// lookup_insert_ne// lookup_insert=>[][->].
      iNext.
      iExists (#1 :: hx), (#1 :: hy), (#1 :: hz).
      iFrame.
      iPureIntro.
      right.
      split; first repeat constructor.
      exists #1, #1.
      do 2 (split; first done).
      by split; left.
    }
    iPoseProof (big_sepM_insert with "mem") as "((x_hx' & _) & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "((y_hy' & _) & mem)"; first done.
    iPoseProof (big_sepM_insert with "mem") as "((z_hz' & _) & _)"; first done.
    iNext.
    iExists hx', hy', hz'.
    iFrame "∗#".
  Qed.

  Lemma transaction2_spec :
    ∀ cst sa,
    client_inv -∗
    {{{ ConnectionState cst CanStart }}}
      transaction2 cst @[ip_of_address sa]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (cst sa) "#inv %Φ!>CanStart HΦ".
    rewrite/transaction2.
    wp_pures.
    wp_apply (SI_start_spec $! _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
    iInv "inv" as ">(%hx & %hy & %hz & x_hx & y_hy & z_hz & init)" "close".
    iModIntro.
    iExists {[ "x" := hx; "y" := hy; "z" := hz ]}.
    iFrame.
    iSplitL "x_hx y_hy z_hz";
      first by repeat (iApply big_sepM_insert; first done; iFrame).
    iIntros "!>(Active & mem & cache & Seen)".
    iMod ("close" with "[mem init]") as "_".
    {
      iNext.
      iExists hx, hy, hz.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz & _)"; first done.
      iFrame.
    }
    iModIntro.
    wp_pures.
    wp_apply (simplified_wait_on_keyT_spec _ _ #1 _ _ _ (⊤ ∖ ↑client_inv_name)
        (λ m, ∃ hx hy hz vx vy, ⌜m !! "x" = Some hx⌝ ∗ ⌜m !! "y" = Some hy⌝ ∗
          ⌜m !! "z" = Some hz⌝ ∗ ⌜#1 ∈ hz⌝ ∗
          ⌜hist_val hx = Some vx⌝ ∗ ⌜hist_val hy = Some vy⌝ ∗
          (⌜vx = #1⌝ ∨ ⌜vx = #(-1)⌝) ∗ (⌜vy = #1⌝ ∨ ⌜vy = #(-1)⌝))%I
          emp emp with
          "[] [] [] [] [] [] [$Active $cache $Seen]"); first solve_ndisj.
    1, 2 : rewrite !dom_insert_L; iPureIntro; set_solver.
    {
      iIntros "!>%h (#Seen & _)".
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          [(_ & _ & ->)|(%hz'_1 & (%vx & %vy & %hx'_vx & %hy'_vy & 
            (%Hvx & %Hvy)))])" "close".
      { iMod (Seen_valid with "[] [$Seen $z_hz']") as "%abs";
          [solve_ndisj|iApply SI_GlobalInv|by apply suffix_nil_inv in abs].
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iSplitR.
      {
        iExists hx', hy', hz', vx, vy.
        iFrame "%".
        by rewrite (lookup_insert_ne _ _ "y").
      }
      iSplitR; first done.
      iIntros "!>(mem & _)".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame.
      iRight.
      iSplit; first done.
      by iExists vx, vy.
    }
    {
      iModIntro.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          %Hinv)" "close".
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}.
      iSplit; first by rewrite !dom_insert_L.
      iSplitL "x_hx' y_hy' z_hz'";
        first by repeat (iApply big_sepM_insert; first done; iFrame).
      iIntros "!>mem".
      iMod ("close" with "[mem]") as "_"; last done.
      iNext.
      iExists hx', hy', hz'.
      iPoseProof (big_sepM_insert with "mem") as "(x_hx' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(y_hy' & mem)"; first done.
      iPoseProof (big_sepM_insert with "mem") as "(z_hz' & _)"; first done.
      iFrame "∗ %".
    }
    {
      iIntros (v' Ψ) "!>_ HΨ".
      wp_pures.
      wp_op; first apply bin_op_eval_eq_val.
      iApply "HΨ".
      by rewrite bool_decide_spec.
    }
    rewrite !dom_insert_L.
    iClear (hx hy hz) "".
    iIntros (m) "(%dom_m & (%hx & %hy & %hz & %vx & %vy & %m_x & %m_y & %m_z &
          %hz_not_empty & %hx_vx & %hy_vy & %Hvx & %Hvy) & Active & cache & Seen)".
    wp_pures.
    iPoseProof (big_sepM_delete _ _ _ _ m_x with "cache") as
        "((x_hx & x_upd) & cache)".
    iPoseProof (big_sepM_delete _ _ "y" hy with "cache") as
        "((y_hy & y_upd) & cache)"; first by rewrite lookup_delete_ne.
    iPoseProof (big_sepM_delete _ _ "z" hz with "cache") as
        "((z_hz & z_upd) & _)"; first by rewrite !lookup_delete_ne.
    iPoseProof (big_sepM_lookup _ _ _ _ m_z with "Seen") as "#Seen_z".
    wp_apply (SI_read_spec with "[] x_hx"); first set_solver.
    iIntros "x_hx".
    rewrite hx_vx hy_vy.
    destruct Hvx as [-> | ->].
    {
      wp_pures.
      wp_apply (SI_write_spec $! _ _ _ _ (SerVal #(-1)) with
          "[] [$y_hy $y_upd]"); first set_solver.
      iIntros "(y_1 & y_upd)".
      wp_pures.
      wp_apply (commitU_spec _ _ (⊤ ∖ ↑client_inv_name)); first solve_ndisj.
      iInv "inv" as ">(%hx' & %hy' & %hz' & x_hx' & y_hy' & z_hz' &
          [(_ & _ & ->)|%Hinv])" "close".
      {
        iMod (Seen_valid $! SI_GlobalInv with "[$Seen_z $z_hz']") as "%abs";
          first solve_ndisj.
        apply suffix_nil_inv in abs.
        rewrite abs in hz_not_empty.
        by apply elem_of_nil in hz_not_empty.
      }
      iModIntro.
      iExists {[ "x" := hx'; "y" := hy'; "z" := hz' ]}, m,
              {[ "x" := (Some #1, false); "y" := (Some #(-1), true);
                  "z" := (hist_val hz, false) ]}.
      iFrame.
      iSplitL "x_hx x_hx' x_upd y_1 y_hy' y_upd z_hz z_hz' z_upd".
      {
        rewrite !dom_insert_L dom_m !dom_empty_L.
        do 2 (iSplit; first done).
        by iSplitL "x_hx' y_hy' z_hz'";
            repeat (iApply big_sepM_insert; first done; iFrame).
      }
      iIntros "!>(_ & [(_ & mem)|(_ & mem)])".
      {
        iMod ("close" with "[mem]") as "_"; last by iApply "HΦ".
        iPoseProof (big_sepM2_insert with "mem") as "((x_hx' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((y_hy' & _) & mem)";
          [done..|].
        iPoseProof (big_sepM2_insert with "mem") as "((z_hz' & _) & _)";
          [done..|].
        have -> : commit_event (hist_val hz, false) hz' = hz'
              by case: (hist_val hz).
  Admitted.

  Lemma server_spec :
    {{{ KVS_Init
      ∗ KVS_address ⤳ (∅, ∅)
      ∗ free_ports (ip_of_address KVS_address) {[port_of_address KVS_address]}
      ∗ KVS_address ⤇ KVS_si }}}
    server #KVS_address @[ip_of_address KVS_address]
    {{{ RET #(); True }}}.
  Proof.
    iIntros (Φ) "(? & ? & ? & ?) HΦ".
    rewrite /server. wp_pures.
    by wp_apply (SI_init_kvs_spec with "[$]").
  Qed.

End proofs.