import OneYTruth.ConstructibleAtomicTruth

/-! A bounded query of a literal stage/truth-set predecessor graph. -/

namespace OneYTruth.PredecessorGraph

open Constructible Constructible.Delta0Formula Constructible.Godel
open CodedPaths BoundedEvaluation

universe u

def Read (q b ξ e a : ZFSet.{u}) : Prop :=
  ∃ T, ZFSet.pair (ZFSet.pair b ξ) T ∈ q ∧ ZFSet.pair e a ∈ T

def readAt {n : Nat} (q b ξ e a : Fin n) : Delta0Formula n :=
  .boundedEx q (.boundedEx (Fin.last n) (.boundedEx (Fin.last (n + 1))
    (.conj (componentEqAt true (Fin.last n).castSucc.castSucc (Fin.last (n + 2)))
      (.conj (pathEqAt [false, false] (Fin.last n).castSucc.castSucc b.castSucc.castSucc.castSucc)
        (.conj (pathEqAt [false, true] (Fin.last n).castSucc.castSucc ξ.castSucc.castSucc.castSucc)
          (pairMemAt (Fin.last (n + 2)) e.castSucc.castSucc.castSucc a.castSucc.castSucc.castSucc))))))

theorem satisfies_readAt {n : Nat} (q b ξ e a : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (readAt q b ξ e a) s ↔ Read (s q) (s b) (s ξ) (s e) (s a) := by
  simp only [readAt, Satisfies, satisfies_componentEqAt, satisfies_pathEqAt,
    satisfies_pairMemAt, snoc_last, snoc_castSucc, Read]
  constructor
  · rintro ⟨p, hp, _, _, T, _, hT, hb, hξ, hea⟩
    obtain ⟨key, rfl⟩ := hT
    simp only [follows_pair, Bool.false_eq_true, if_false] at hb hξ
    obtain ⟨key', hkey, hkb⟩ := hb
    obtain ⟨tail, hk⟩ := hkey
    change key' = s b at hkb
    subst key'
    rw [hk, follows_pair, if_pos rfl] at hξ
    change tail = s ξ at hξ
    subst tail
    exact ⟨T, hk ▸ hp, hea⟩
  · rintro ⟨T, hp, hea⟩
    have hc : Component true (ZFSet.pair (ZFSet.pair (s b) (s ξ)) T) T := ⟨_, rfl⟩
    obtain ⟨box, hbox, hT⟩ := component_bounded hc
    refine ⟨_, hp, box, hbox, T, hT, hc, ?_, ?_, hea⟩
    all_goals simp [follows_pair, Follows]

end OneYTruth.PredecessorGraph
