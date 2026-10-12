/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Group.Prod
public import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Tactic.CrossRefAttribute

/-!
# The diagonal and difference maps of an additive group

@stack 00JG

For an additive commutative group `A`, the difference map `(a, b) ↦ b - a` is
surjective and its kernel is the range of the diagonal map `a ↦ (a, a)`.  This
file packages the maps and their exactness as reusable `AddMonoidHom` API.
-/

@[expose] public section

universe u

namespace MonoidHom

variable (G : Type u) [CommGroup G]

/-- The quotient of the second coordinate by the first. -/
@[stacks 00JG "ratio of two endpoint coordinates"]
def sndDivFst : G × G →* G :=
  snd G G * (fst G G)⁻¹

/-- The diagonal homomorphism into a product. -/
@[stacks 00JG "diagonal endpoint coordinates"]
def diagonal : G →* G × G :=
  (id G).prod (id G)

@[simp]
theorem sndDivFst_apply (p : G × G) : sndDivFst G p = p.2 * p.1⁻¹ :=
  rfl

@[simp]
theorem diagonal_apply (g : G) : diagonal G g = (g, g) :=
  rfl

/-- Every element is the ratio of the pair `(1, g)`. -/
@[stacks 00JG "surjectivity of the endpoint ratio"]
theorem sndDivFst_surjective : Function.Surjective (sndDivFst G) := by
  intro g
  exact ⟨(1, g), by simp⟩

/-- A pair has trivial ratio exactly when its coordinates agree. -/
@[simp]
theorem sndDivFst_eq_one_iff (p : G × G) :
    sndDivFst G p = 1 ↔ p.2 = p.1 := by
  rw [sndDivFst_apply, mul_inv_eq_one]

/-- The diagonal pairs are exactly the kernel of the endpoint ratio. -/
@[stacks 00JG "exact diagonal-ratio sequence"]
theorem diagonal_range_eq_sndDivFst_ker :
    (diagonal G).range = (sndDivFst G).ker := by
  ext p
  change (∃ g, diagonal G g = p) ↔ sndDivFst G p = 1
  constructor
  · rintro ⟨g, rfl⟩
    simp
  · intro hp
    have hp' : p.2 = p.1 := (sndDivFst_eq_one_iff G p).mp hp
    exact ⟨p.1, by ext <;> simp [hp']⟩

/-- The additive form of the diagonal-ratio exactness statement. -/
@[stacks 00JG "additive exact diagonal-ratio sequence"]
theorem toAdditive_diagonal_range_eq_sndDivFst_ker :
    (diagonal G).toAdditive.range = (sndDivFst G).toAdditive.ker := by
  ext p
  change (∃ g : Additive G, (diagonal G).toAdditive g = p) ↔
    (sndDivFst G).toAdditive p = 0
  constructor
  · rintro ⟨g, rfl⟩
    simp
  · intro hp
    have hp' : p.toMul.2 = p.toMul.1 := by
      exact (sndDivFst_eq_one_iff G p.toMul).mp hp
    exact ⟨Additive.ofMul p.toMul.1, by ext <;> simp [hp']⟩

end MonoidHom

namespace AddMonoidHom

variable (A : Type u) [AddCommGroup A]

/-- The difference of the second and first coordinates. -/
@[stacks 00JG "difference of two endpoint coordinates"]
def sndSubFst : A × A →+ A :=
  snd A A - fst A A

/-- The diagonal homomorphism into a product. -/
@[stacks 00JG "diagonal endpoint coordinates"]
def diagonal : A →+ A × A :=
  (id A).prod (id A)

@[simp]
theorem sndSubFst_apply (p : A × A) : sndSubFst A p = p.2 - p.1 :=
  rfl

@[simp]
theorem diagonal_apply (a : A) : diagonal A a = (a, a) :=
  rfl

/-- Every element is the difference of the pair `(0, a)`. -/
@[stacks 00JG "surjectivity of the coordinate difference"]
theorem sndSubFst_surjective : Function.Surjective (sndSubFst A) := by
  intro a
  exact ⟨(0, a), by simp⟩

/-- A pair has zero difference exactly when its coordinates agree. -/
@[simp]
theorem sndSubFst_eq_zero_iff (p : A × A) :
    sndSubFst A p = 0 ↔ p.2 = p.1 := by
  rw [sndSubFst_apply, sub_eq_zero]

/-- The diagonal pairs are exactly the kernel of the coordinate difference. -/
@[stacks 00JG "exact diagonal-difference sequence"]
theorem diagonal_range_eq_sndSubFst_ker :
    (diagonal A).range = (sndSubFst A).ker := by
  ext p
  change (∃ a, diagonal A a = p) ↔ sndSubFst A p = 0
  constructor
  · rintro ⟨a, rfl⟩
    simp
  · intro hp
    have hp' : p.2 = p.1 := (sndSubFst_eq_zero_iff A p).mp hp
    exact ⟨p.1, by ext <;> simp [hp']⟩

end AddMonoidHom
