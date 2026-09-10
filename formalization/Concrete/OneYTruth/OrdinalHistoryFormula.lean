import OneYTruth.OrdinalHistoryRaw

/-! # Literal bounded syntax for the ordinal-history clauses

Every displayed quantifier is bounded by the index set, history, a supplied
field container, or a set already stored in that container. The successor
test remains a supplied Delta0 matrix until the canonical Def certificate
has been compiled under the common witness bound.
-/

namespace OneYTruth.OrdinalStageHistory

open Constructible Constructible.Model Constructible.Delta0Formula

universe u

def entryAt {n : Nat} (g i U : Fin n) : Delta0Formula n :=
  .boundedEx g (kuratowskiPairEqAt (Fin.last n) i.castSucc U.castSucc)

theorem satisfies_entryAt {n : Nat} (g i U : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (entryAt g i U) s ↔ ZFSet.pair (s i) (s U) ∈ s g := by
  simp only [entryAt, Satisfies, satisfies_kuratowskiPairEqAt, snoc_last, snoc_castSucc]
  exact ⟨fun ⟨p, hp, he⟩ => he ▸ hp, fun h => ⟨_, h, rfl⟩⟩

def emptyAt {n : Nat} (U : Fin n) : Delta0Formula n :=
  .boundedAll U (.neg (.eq (Fin.last n) (Fin.last n)))

theorem satisfies_emptyAt {n : Nat} (U : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (emptyAt U) s ↔ s U = ∅ := by
  simp only [emptyAt, satisfies_boundedAll, Satisfies]
  constructor
  · intro h
    apply ZFSet.ext
    intro x
    exact ⟨fun hx => (h x hx True.intro).elim, fun hx => (ZFSet.notMem_empty x hx).elim⟩
  · intro h x hx
    exact (ZFSet.notMem_empty x (h ▸ hx)).elim

def rawLimitAt {n : Nat} (i : Fin n) : Delta0Formula n :=
  .conj (.neg (emptyAt i)) (.boundedAll i (.neg (successorAt i.castSucc (Fin.last n))))

theorem satisfies_rawLimitAt {n : Nat} (i : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (rawLimitAt i) s ↔ RawLimit (s i) := by
  simp only [rawLimitAt, Satisfies, satisfies_emptyAt, satisfies_boundedAll,
    satisfies_successorAt, snoc_castSucc, snoc_last]
  rfl

def totalAt {n : Nat} (I g B : Fin n) : Delta0Formula n :=
  .boundedAll I (.boundedEx B.castSucc
    (entryAt g.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1))))

theorem satisfies_totalAt {n : Nat} (I g B : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (totalAt I g B) s ↔ ∀ i ∈ s I, ∃ U ∈ s B, ZFSet.pair i U ∈ s g := by
  simp only [totalAt, satisfies_boundedAll, Satisfies, satisfies_entryAt,
    snoc_castSucc, snoc_last]

def noJunkAt {n : Nat} (I g B : Fin n) : Delta0Formula n :=
  .boundedAll g (.boundedEx I.castSucc (.boundedEx B.castSucc.castSucc
    (kuratowskiPairEqAt (Fin.last n).castSucc.castSucc
      (Fin.last (n+1)).castSucc (Fin.last (n+2)))))

theorem satisfies_noJunkAt {n : Nat} (I g B : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (noJunkAt I g B) s ↔
      ∀ p ∈ s g, ∃ i ∈ s I, ∃ U ∈ s B, p = ZFSet.pair i U := by
  simp only [noJunkAt, satisfies_boundedAll, Satisfies, satisfies_kuratowskiPairEqAt,
    snoc_castSucc, snoc_last]

def zeroAt {n : Nat} (g B Z : Fin n) : Delta0Formula n :=
  .boundedAll B (.imp (entryAt g.castSucc Z.castSucc (Fin.last n)) (emptyAt (Fin.last n)))

theorem satisfies_zeroAt {n : Nat} (g B Z : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (zeroAt g B Z) s ↔
      ∀ U ∈ s B, ZFSet.pair (s Z) U ∈ s g → U = ∅ := by
  simp only [zeroAt, satisfies_boundedAll, satisfies_imp, satisfies_entryAt,
    satisfies_emptyAt, snoc_castSucc, snoc_last]

def unionBelowAt {n : Nat} (i g B U : Fin n) : Delta0Formula n :=
  .conj
    (.boundedAll U (.boundedEx i.castSucc (.boundedEx B.castSucc.castSucc
      (.conj (entryAt g.castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc (Fin.last (n+2)))
        (.mem (Fin.last n).castSucc.castSucc (Fin.last (n+2)))))))
    (.boundedAll i (.boundedAll B.castSucc
      (.imp (entryAt g.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1)))
        (subsetAt (Fin.last (n+1)) U.castSucc.castSucc))))

theorem satisfies_unionBelowAt {n : Nat} (i g B U : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (unionBelowAt i g B U) s ↔
      ∀ z, z ∈ s U ↔ ∃ j ∈ s i, ∃ T ∈ s B, ZFSet.pair j T ∈ s g ∧ z ∈ T := by
  simp only [unionBelowAt, Satisfies, satisfies_boundedAll, satisfies_imp, satisfies_entryAt,
    satisfies_subsetAt, snoc_castSucc, snoc_last]
  constructor
  · rintro ⟨hl, hr⟩ z
    exact ⟨hl z, fun ⟨j, hj, T, hT, he, hz⟩ => hr j hj T hT he hz⟩
  · intro h
    refine ⟨fun z hz => (h z).mp hz, ?_⟩
    intro j hj T hT he z hz
    exact (h z).mpr ⟨j, hj, T, hT, he, hz⟩

def limitAt {n : Nat} (I g B : Fin n) : Delta0Formula n :=
  .boundedAll I (.imp (rawLimitAt (Fin.last n))
    (.boundedAll B.castSucc
      (.imp (entryAt g.castSucc.castSucc (Fin.last n).castSucc (Fin.last (n+1)))
        (unionBelowAt (Fin.last n).castSucc g.castSucc.castSucc B.castSucc.castSucc (Fin.last (n+1))))))

theorem satisfies_limitAt {n : Nat} (I g B : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (limitAt I g B) s ↔
      ∀ i ∈ s I, RawLimit i → ∀ U ∈ s B, ZFSet.pair i U ∈ s g →
        ∀ z, z ∈ U ↔ ∃ j ∈ i, ∃ T ∈ s B, ZFSet.pair j T ∈ s g ∧ z ∈ T := by
  simp only [limitAt, satisfies_boundedAll, satisfies_imp, satisfies_rawLimitAt,
    satisfies_entryAt, satisfies_unionBelowAt, snoc_castSucc, snoc_last]

def stepAt {p n : Nat} (step : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (U D : Fin n) : Delta0Formula n :=
  step.rename (Fin.lastCases D (Fin.lastCases U params))

theorem satisfies_stepAt {p n : Nat} (step : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (U D : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (stepAt step params U D) s ↔
      Satisfies ZFMem step (snoc (snoc (fun i => s (params i)) (s U)) (s D)) := by
  rw [stepAt, satisfies_rename]
  have he : (fun i => s (Fin.lastCases D (Fin.lastCases U params) i)) =
      snoc (snoc (fun i => s (params i)) (s U)) (s D) := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp only [Fin.lastCases_last, snoc_last]
    · refine Fin.lastCases ?_ (fun k => ?_) j
      · simp only [Fin.lastCases_castSucc, Fin.lastCases_last, snoc_castSucc, snoc_last]
      · simp only [Fin.lastCases_castSucc, snoc_castSucc]
  rw [he]

def successorClauseAt {p n : Nat} (step : Delta0Formula (p+2))
    (params : Fin p → Fin n) (I g B : Fin n) : Delta0Formula n :=
  .boundedAll I (.boundedAll I.castSucc
    (.imp (successorAt (Fin.last (n+1)) (Fin.last n).castSucc)
      (.boundedAll B.castSucc.castSucc (.boundedAll B.castSucc.castSucc.castSucc
        (.imp (.conj
          (entryAt g.castSucc.castSucc.castSucc.castSucc (Fin.last n).castSucc.castSucc.castSucc
            (Fin.last (n+2)).castSucc)
          (entryAt g.castSucc.castSucc.castSucc.castSucc (Fin.last (n+1)).castSucc.castSucc
            (Fin.last (n+3))))
          (stepAt step (fun i => (params i).castSucc.castSucc.castSucc.castSucc)
            (Fin.last (n+2)).castSucc (Fin.last (n+3))))))))

theorem satisfies_successorClauseAt {p n : Nat} (step : Delta0Formula (p+2))
    (params : Fin p → Fin n) (I g B : Fin n) (s : Tuple ZFSet.{u} n) :
    Satisfies ZFMem (successorClauseAt step params I g B) s ↔
      ∀ i ∈ s I, ∀ j ∈ s I, j = insert i i → ∀ U ∈ s B, ∀ D ∈ s B,
        ZFSet.pair i U ∈ s g → ZFSet.pair j D ∈ s g →
          Satisfies ZFMem step (snoc (snoc (fun i => s (params i)) U) D) := by
  simp only [successorClauseAt, satisfies_boundedAll, satisfies_imp, satisfies_successorAt,
    Satisfies, satisfies_entryAt, satisfies_stepAt, snoc_castSucc, snoc_last]
  exact ⟨fun h i hi j hj hs U hU D hD he hf => h i hi j hj hs U hU D hD ⟨he, hf⟩,
    fun h i hi j hj hs U hU D hD ⟨he, hf⟩ => h i hi j hj hs U hU D hD he hf⟩

def historyAt {p n : Nat} (step : Delta0Formula (p+2)) (params : Fin p → Fin n)
    (I g B Z : Fin n) : Delta0Formula n :=
  .conj (totalAt I g B) (.conj (noJunkAt I g B) (.conj (zeroAt g B Z)
    (.conj (successorClauseAt step params I g B) (limitAt I g B))))

theorem satisfies_historyAt {p n : Nat} (step : Delta0Formula (p+2))
    (params : Fin p → Fin n) (I g B Z : Fin n) (s : Tuple ZFSet.{u} n) (hzero : s Z = ∅) :
    Satisfies ZFMem (historyAt step params I g B Z) s ↔
      RawChecks (fun U D => Satisfies ZFMem step
        (snoc (snoc (fun i => s (params i)) U) D)) (s I) (s g) (s B) := by
  simp only [historyAt, Satisfies, satisfies_totalAt, satisfies_noJunkAt, satisfies_zeroAt,
    satisfies_successorClauseAt, satisfies_limitAt, hzero]
  exact ⟨fun ⟨ht, hn, hz, hs, hl⟩ => ⟨ht, hn, hz, hs, hl⟩,
    fun h => ⟨h.total, h.noJunk, h.zero, h.successor, h.limit⟩⟩

/-- The successor step is still a supplied bounded matrix. The complete
history skeleton itself is now a literal Delta0 formula. -/
def historyFormula {p : Nat} (step : Delta0Formula (p+2)) : Delta0Formula (p+4) :=
  historyAt step (fun i => i.castSucc.castSucc.castSucc.castSucc)
    (Fin.last p).castSucc.castSucc.castSucc (Fin.last (p+1)).castSucc.castSucc
    (Fin.last (p+2)).castSucc (Fin.last (p+3))

theorem satisfies_historyFormula {p : Nat} (step : Delta0Formula (p+2))
    (params : Tuple ZFSet.{u} p) (I g B : ZFSet.{u}) :
    Satisfies ZFMem (historyFormula step)
      (snoc (snoc (snoc (snoc params I) g) B) ∅) ↔
      RawChecks (fun U D => Satisfies ZFMem step (snoc (snoc params U) D)) I g B := by
  simpa only [historyFormula, snoc_castSucc, snoc_last] using
    (satisfies_historyAt step (fun i => i.castSucc.castSucc.castSucc.castSucc)
      (Fin.last p).castSucc.castSucc.castSucc (Fin.last (p+1)).castSucc.castSucc
      (Fin.last (p+2)).castSucc (Fin.last (p+3))
      (snoc (snoc (snoc (snoc params I) g) B) ∅) (by simp only [snoc_last]))

end OneYTruth.OrdinalStageHistory

#print axioms OneYTruth.OrdinalStageHistory.satisfies_historyFormula


