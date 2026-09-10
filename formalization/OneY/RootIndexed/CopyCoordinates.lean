import OneY.RootIndexed.Representation
import OneY.CopyCoordinates

/-! # Actual copy coordinates for the finite reflection scheme -/

namespace OneY.RootIndexed

def blockCut (C : CopyCoordinates.Context) (b : Nat) : Nat := C.y+b*C.length

theorem blockCut_lt_width (C : CopyCoordinates.Context) (b : Nat) :
    blockCut C b < C.width b := by
  have := C.root_lt_last
  unfold blockCut CopyCoordinates.Context.width
  omega

theorem blockCut_succ (C : CopyCoordinates.Context) (b : Nat) :
    blockCut C (b+1) = C.width b := by
  have := C.root_add_length
  unfold blockCut CopyCoordinates.Context.width
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem width_succ (C : CopyCoordinates.Context) (b : Nat) :
    C.width (b+1) = C.width b+(C.width b-blockCut C b) := by
  have := C.root_add_length
  unfold blockCut CopyCoordinates.Context.width
  rw [Nat.add_mul, Nat.one_mul]
  omega

theorem parentCopy_strict_mono (C : CopyCoordinates.Context) (b : Nat)
    {p q : Nat} (hpq : p < q) : C.parentCopy b p < C.parentCopy b q := by
  unfold CopyCoordinates.Context.parentCopy
  split <;> split <;> omega

theorem parentCopy_mono (C : CopyCoordinates.Context) (b : Nat)
    {p q : Nat} (hpq : p ≤ q) : C.parentCopy b p ≤ C.parentCopy b q := by
  rcases Nat.lt_or_eq_of_le hpq with h | rfl
  · exact Nat.le_of_lt (parentCopy_strict_mono C b h)
  · exact Nat.le_refl _

theorem parentCopy_lt_width (C : CopyCoordinates.Context) (b : Nat)
    {p : Nat} (hp : p < C.x) : C.parentCopy b p < C.width b := by
  unfold CopyCoordinates.Context.parentCopy CopyCoordinates.Context.width
  split <;> omega

theorem parentCopy_le_cut (C : CopyCoordinates.Context) (b : Nat)
    {p : Nat} (hp : p ≤ C.y) : C.parentCopy b p ≤ blockCut C b := by
  have := parentCopy_mono C b hp
  simpa only [C.parentCopy_bad b (Nat.le_refl C.y), blockCut] using this

theorem moveColumn_parentCopy (C : CopyCoordinates.Context) (b p : Nat) :
    moveColumn (C.width b) (blockCut C b) (C.parentCopy b p) = C.parentCopy (b+1) p := by
  have hxy := C.root_add_length
  unfold moveColumn CopyCoordinates.Context.parentCopy CopyCoordinates.Context.width blockCut
  by_cases hp : p < C.y
  · simp only [hp, ↓reduceIte]
    rw [if_pos (by omega)]
  · simp only [hp, ↓reduceIte]
    rw [if_neg (by omega), Nat.add_mul, Nat.one_mul]
    omega

def copyAtom (C : CopyCoordinates.Context) (b : Nat) (e : Atom) : Atom :=
  { e with root := C.parentCopy b e.root
           parent := C.parentCopy b e.parent
           child := C.parentCopy b e.child }

def copyTopAtom (C : CopyCoordinates.Context) (b : Nat) (e : TopAtom) : TopAtom :=
  { e with root := C.parentCopy b e.root
           parent := C.parentCopy b e.parent }

theorem copyAtom_zero (C : CopyCoordinates.Context) (e : Atom) : copyAtom C 0 e = e := by
  cases e
  simp [copyAtom, C.parentCopy_zero]

theorem copyTopAtom_zero (C : CopyCoordinates.Context) (e : TopAtom) :
    copyTopAtom C 0 e = e := by
  cases e
  simp [copyTopAtom, C.parentCopy_zero]

theorem copyAtom_valid (C : CopyCoordinates.Context) (b : Nat) {e : Atom}
    (he : e.Valid C.x) : (copyAtom C b e).Valid (C.width b) :=
  ⟨parentCopy_mono C b he.1, parentCopy_strict_mono C b he.2.1,
    parentCopy_lt_width C b he.2.2⟩

theorem copyTopAtom_valid (C : CopyCoordinates.Context) (b : Nat) {e : TopAtom}
    (he : e.Valid C.x) : (copyTopAtom C b e).Valid (C.width b) :=
  ⟨parentCopy_mono C b he.1, parentCopy_lt_width C b he.2⟩

theorem moveAtom_copyAtom (C : CopyCoordinates.Context) (b : Nat) (e : Atom) :
    moveAtom (C.width b) (blockCut C b) (copyAtom C b e) = copyAtom C (b+1) e := by
  simp only [moveAtom, copyAtom, moveColumn_parentCopy]

theorem moveTopAtom_copyTopAtom (C : CopyCoordinates.Context) (b : Nat) (e : TopAtom) :
    moveTopAtom (C.width b) (blockCut C b) (copyTopAtom C b e) = copyTopAtom C (b+1) e := by
  simp only [moveTopAtom, copyTopAtom, moveColumn_parentCopy]

end OneY.RootIndexed

#print axioms OneY.RootIndexed.moveAtom_copyAtom
