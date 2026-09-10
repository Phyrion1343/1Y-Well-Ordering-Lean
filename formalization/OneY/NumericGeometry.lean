import OneY.Numeric
import OneY.ForestBridge
import OneY.RootGeometry
import ZeroY.Mountain.Roots

/-!
# The numerical 1-Y mountain satisfies the leg geometry

Both column heights and row component roots are computed, rather than
postulated. The only positivity input is positivity of the base row.
-/

namespace OneY.Numeric

theorem select_refines (frame : ParentForest) (value : Nat → Nat) :
    (select frame value).forest.Refines frame := by
  intro c p hp
  exact ParentForest.ancestor_of_zeroY (restrictedParent_spec frame value hp).1

theorem Row.next_refines (a : Row) : a.next.forest.Refines a.forest :=
  select_refines a.forest a.difference

def mountain (base : Row) (hbase : ∀ c, 0 < base.value c) :
    RootGeometry.RowMountain where
  height := height base
  row r := (rows base r).forest
  parent_exists r c hr := (parent_exists_iff_lt_height base (hbase c) r).mpr hr
  parent_source hp := (parent_exists_iff_lt_height base (hbase _) _).mp ⟨_, hp⟩
  parent_endpoint := parent_endpoint base hbase
  nested_succ r := (rows base r).next_refines

def geometry (base : Row) (hbase : ∀ c, 0 < base.value c) : Geometry.Mountain :=
  (mountain base hbase).toMountain

theorem vertex_iff_computed_root (base : Row) (hbase : ∀ c, 0 < base.value c)
    (y c : Nat) :
    Geometry.Reach (geometry base hbase) y (height base c) c ↔
      height base y ≤ height base c ∧
        (rows base (height base y)).forest.root c = y :=
  (mountain base hbase).vertex_iff y c

theorem contour_iff_computed_root (base : Row) (hbase : ∀ c, 0 < base.value c)
    (y r c : Nat) :
    Geometry.Contour (geometry base hbase) y r c ↔
      r < height base c ∧ height base y ≤ r ∧
        (rows base (height base y)).forest.root c = y := by
  unfold geometry
  rw [(mountain base hbase).contour_iff]
  change (r < height base c ∧ height base y ≤ r ∧
    height base y ≤ height base c ∧
      (rows base (height base y)).forest.root c = y) ↔ _
  constructor
  · rintro ⟨hc, hy, _, he⟩; exact ⟨hc, hy, he⟩
  · rintro ⟨hc, hy, he⟩; exact ⟨hc, hy, by omega, he⟩

theorem reference_iff_computed_root (base : Row) (hbase : ∀ c, 0 < base.value c)
    (y r c : Nat) :
    Geometry.Reference (geometry base hbase) y r c ↔
      r = height base y ∧ r < height base c ∧
        (rows base (height base y)).forest.root c = y := by
  rw [Geometry.reference_iff]
  change (r = height base y ∧ r < height base c ∧
    height base y ≤ height base c ∧
      (rows base (height base y)).forest.root c = y) ↔ _
  constructor
  · rintro ⟨hr, hc, _, he⟩; exact ⟨hr, hc, he⟩
  · rintro ⟨hr, hc, he⟩; exact ⟨hr, hc, by omega, he⟩

def linearForest : ParentForest where
  parent := ZeroY.linearParent
  parent_left := ZeroY.linearParent_leftward

/-- Padding by ones makes a total row without adding a parent edge at any
new column. Only the original finite prefix represents the input sequence. -/
def ofSequence (s : List Nat) : Row :=
  select linearForest fun c => s[c]?.getD 1

theorem ofSequence_positive (s : List Nat) (hs : ∀ x ∈ s, 0 < x) (c : Nat) :
    0 < (ofSequence s).value c := by
  change 0 < s[c]?.getD 1
  cases hv : s[c]? with
  | none => simp
  | some v =>
      simp only [Option.getD_some]
      exact hs v (List.mem_of_getElem? hv)

def sequenceMountain (s : List Nat) (hs : ∀ x ∈ s, 0 < x) :
    RootGeometry.RowMountain := mountain (ofSequence s) (ofSequence_positive s hs)

theorem ofSequence_no_padding_parent (s : List Nat) {c : Nat} (hc : s.length ≤ c) :
    (ofSequence s).forest.parent c = none := by
  have hval : (ofSequence s).value c = 1 := by
    simp [ofSequence, select, List.getElem?_eq_none hc]
  cases hp : (ofSequence s).forest.parent c with
  | none => rfl
  | some p =>
      have hv := (ofSequence s).parent_values hp
      omega

end OneY.Numeric

#print axioms OneY.Numeric.mountain
#print axioms OneY.Numeric.contour_iff_computed_root
#print axioms OneY.Numeric.reference_iff_computed_root
