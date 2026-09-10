import OneYTruth.InitialCanonicalSupply
import OneY.RootIndexed.Representation

/-!
# Actual initial finite root-indexed representations

The label chain is constructed from the concrete auxiliary elementary
stages. The sole unresolved supply hypothesis here is constructibility
of the actual ambient truth set, needed for endpoint Separation.
-/

namespace OneYTruth.RootSemantics

open Constructible InitialStage
open scoped Ordinal

universe u

noncomputable def nextEndpoint (γ : Index.{u}) : Index.{u} :=
  ⟨Classical.choose (exists_initialEndpoint_above γ),
    (Classical.choose_spec (exists_initialEndpoint_above γ)).1.1⟩

theorem nextEndpoint_mem (γ : Index.{u}) : (nextEndpoint γ).val ∈ initialClub :=
  (Classical.choose_spec (exists_initialEndpoint_above γ)).1

theorem lt_nextEndpoint (γ : Index.{u}) : γ.val < (nextEndpoint γ).val :=
  (Classical.choose_spec (exists_initialEndpoint_above γ)).2.1

theorem omega_lt_nextEndpoint (γ : Index.{u}) : Ordinal.omega0 < (nextEndpoint γ).val :=
  (Classical.choose_spec (exists_initialEndpoint_above γ)).2.2

noncomputable def endpointChain (γ : Index.{u}) : Nat → Index.{u}
  | 0 => nextEndpoint γ
  | n + 1 => nextEndpoint (endpointChain γ n)

theorem endpointChain_strictMono (γ : Index.{u}) :
    StrictMono (fun n => (endpointChain γ n).val) :=
  strictMono_nat_of_lt_succ (fun n => lt_nextEndpoint (endpointChain γ n))

theorem endpointChain_mem (γ : Index.{u}) (n : Nat) :
    (endpointChain γ n).val ∈ initialClub := by
  cases n with
  | zero => exact nextEndpoint_mem γ
  | succ n => exact nextEndpoint_mem (endpointChain γ n)

theorem omega_lt_endpointChain (γ : Index.{u}) (n : Nat) :
    Ordinal.omega0 < (endpointChain γ n).val := by
  cases n with
  | zero => exact omega_lt_nextEndpoint γ
  | succ n => exact omega_lt_nextEndpoint (endpointChain γ n)

theorem endpointChain_representation (hW : ambientTruth.{u} ∈ L) (γ : Index.{u})
    (G : OneY.RootIndexed.Diagram) :
    OneY.RootIndexed.Representation (· < ·) Adequate R G
      (fun n => (endpointChain γ n).val) := by
  constructor
  · intro i _
    exact initialClub_adequate hW (endpointChain_mem γ i) (omega_lt_endpointChain γ i)
  · intro i j hij _
    exact endpointChain_strictMono γ hij
  · intro e he
    obtain ⟨hrp, hpc, _⟩ := G.valid e he
    exact initialClub_relation (endpointChain_mem γ e.parent) (endpointChain_mem γ e.child)
      (endpointChain_strictMono γ hpc) ((endpointChain_strictMono γ).monotone hrp) e.layer

theorem exists_initial_representation (hW : ambientTruth.{u} ∈ L)
    (G : OneY.RootIndexed.Diagram) :
    ∃ f : Nat → Ordinal.{u}, OneY.RootIndexed.Representation (· < ·) Adequate R G f :=
  ⟨fun n => (endpointChain ⟨0, Ordinal.omega0_pos.trans Ordinal.omega0_lt_omega_one⟩ n).val,
    endpointChain_representation hW _ G⟩

end OneYTruth.RootSemantics
