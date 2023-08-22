From iris.algebra Require Import agree auth excl gmap updates local_updates.
From iris.algebra.lib Require Import mono_list.
From iris.base_logic.lib Require Import mono_nat ghost_map.
From iris.base_logic Require Import invariants.
From iris.bi.lib Require Import fractional.
From iris.proofmode Require Import tactics.
From aneris.prelude Require Import list.
From aneris.algebra Require Import monotone.
From aneris.aneris_lang Require Import lang resources resources inject.
From aneris.lib Require Import gen_heap_light.
From aneris.aneris_lang.lib Require Import
     list_proof monitor_proof lock_proof map_proof.
From aneris.aneris_lang.lib.serialization Require Import serialization_proof.
From aneris.examples.snapshot_isolation.specs Require Import user_params.
From aneris.examples.snapshot_isolation.proof Require Import
     time events model.
From aneris.examples.snapshot_isolation.proof.resources Require Import
     resource_algebras server_resources.

Section Local_Invariant.

  Context `{!anerisG Mdl Σ, !User_params, !IDBG Σ}.
  Context (γGauth γT : gname).

  Definition lkResDef : iProp Σ :=
    ∃ (kvsL vnumL: loc) (kvsV : val) (T: Time)
      (m : gmap Key val) (M : gmap Key (list write_event)) ,
      ⌜is_map kvsV m⌝ ∗
        ⌜kvsl_valid m M T⌝ ∗
        ownMemAuthLocal γGauth M ∗
        ownTimeLocal γT T ∗
        kvsL ↦[ip_of_address KVS_address] kvsV ∗
        vnumL ↦[ip_of_address KVS_address] #T.

  Definition server_lock_inv (γ : gname) (v : val) : iProp Σ :=
    is_lock (KVS_InvName .@ "lk") (ip_of_address KVS_address) γ v (lkResDef).

End Local_Invariant.
