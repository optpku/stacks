module

public import Mathlib.Algebra.CharP.Two
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.FieldTheory.RatFunc.Basic
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.Algebra.Group.Subgroup.Lattice
public import ReasLib.AlgebraicGeometry.FormalDeformation.DualNumber.Quotient

/-!
# Frobenius shear of the dual numbers over a rational function field

Over the rational function field in characteristic two, differentiation vanishes
on the square subfield. The shear adding the derivative of the scalar coordinate
to the infinitesimal coordinate is a residue-preserving involution fixing epsilon.
Its two-element automorphism subgroup gives a smooth versal orbit quotient with
bijective differential on derivation orbits that fails Schlessinger's condition (S2).
-/

@[expose] public section

noncomputable section

open CategoryTheory TrivSqZeroExt IsLocalRing ArtinianLocalAlgCat

namespace ArtinianLocalAlgCat.FrobeniusShear

/-- The rational function field in one variable over the two-element field. -/
abbrev k := RatFunc (ZMod 2)

/-- The subfield of squares, equivalently `F₂(t²)`. -/
def squareSubfield : Subfield k := (frobenius k 2).fieldRange

/-- The base field with its canonical subfield operations and inclusion in `k`. -/
abbrev Λ := squareSubfield

/-- The transcendental generator of `k`. -/
def t : k := algebraMap (Polynomial (ZMod 2)) k Polynomial.X

/-- The ordinary rational derivative, using the normalized numerator and denominator. -/
def derivative (a : k) : k :=
  (algebraMap (Polynomial (ZMod 2)) k a.num.derivative *
      algebraMap (Polynomial (ZMod 2)) k a.denom -
    algebraMap (Polynomial (ZMod 2)) k a.num *
      algebraMap (Polynomial (ZMod 2)) k a.denom.derivative) /
    (algebraMap (Polynomial (ZMod 2)) k a.denom) ^ 2

/-- Additivity of the specified quotient-rule derivative. -/
theorem derivative_add (a b : k) :
    derivative (a + b) = derivative a + derivative b := sorry

/-- The product rule for the specified quotient-rule derivative. -/
theorem derivative_mul (a b : k) :
    derivative (a * b) = a * derivative b + b * derivative a := sorry

/-- The rational derivative annihilates zero. -/
@[simp] theorem derivative_zero : derivative 0 = 0 := by
  simp [derivative]

/-- The rational derivative annihilates one. -/
@[simp] theorem derivative_one : derivative 1 = 0 := by
  simp [derivative]

/-- The derivative of the actual rational-function variable is one. -/
@[simp] theorem derivative_t : derivative t = 1 := by
  simp [derivative, t]

/-- Squares have zero derivative in characteristic two. -/
theorem derivative_square (a : k) : derivative (a ^ 2) = 0 := by
  rw [pow_two, derivative_mul, CharTwo.add_self_eq_zero]

/-- Every scalar in the image subfield is killed by the derivative. -/
theorem derivative_base (r : Λ) : derivative (algebraMap Λ k r) = 0 := by
  obtain ⟨a, ha⟩ := r.property
  change derivative (r : k) = 0
  rw [← ha]
  exact derivative_square a

/-- Linearity over the square subfield follows from its vanishing derivative. -/
theorem derivative_smul (r : Λ) (a : k) :
    derivative (r • a) = r • derivative a := by
  change derivative (algebraMap Λ k r * a) = algebraMap Λ k r * derivative a
  rw [derivative_mul, derivative_base, mul_zero, add_zero]

/-- The nonzero `Λ`-derivation with its concrete quotient-rule function. -/
def D : Derivation Λ k k where
  toFun := derivative
  map_add' := derivative_add
  map_smul' := derivative_smul
  map_one_eq_zero' := derivative_one
  leibniz' := derivative_mul

/-- The bundled derivation evaluates by the explicit rational formula. -/
@[simp] theorem D_apply (a : k) : D a = derivative a := rfl

/-- The derivative is nonzero because it takes value one on the transcendental generator. -/
theorem D_ne_zero : D ≠ 0 := by
  intro h
  have ht := congrArg (fun d : Derivation Λ k k ↦ d t) h
  simp at ht

/-- The rational function field is finite over its square subfield. -/
instance finiteExtension : Module.Finite Λ k := sorry

/-- The degree of the square-subfield extension is exactly two. -/
theorem finrank_base : Module.finrank Λ k = 2 := sorry

/-- The explicit shear map on dual numbers fixes residue and adds `D(a)` to the ε coordinate. -/
def shearMap : DualNumber k →ₐ[Λ] DualNumber k where
  toFun x := ⟨x.fst, derivative x.fst + x.snd⟩
  map_zero' := by
    apply TrivSqZeroExt.ext <;> simp
  map_one' := by
    apply TrivSqZeroExt.ext <;> simp
  map_add' := by
    intro x y
    apply TrivSqZeroExt.ext
    · rfl
    · change derivative (x.fst + y.fst) + (x.snd + y.snd) =
        (derivative x.fst + x.snd) + (derivative y.fst + y.snd)
      rw [derivative_add]
      ac_rfl
  map_mul' := by
    intro x y
    apply TrivSqZeroExt.ext
    · rfl
    · change derivative (x.fst * y.fst) + (x.fst * y.snd + x.snd * y.fst) =
        x.fst * (derivative y.fst + y.snd) + (derivative x.fst + x.snd) * y.fst
      rw [derivative_mul]
      ring
  commutes' := by
    intro r
    apply TrivSqZeroExt.ext
    · rfl
    · change derivative (algebraMap Λ k r) + 0 = 0
      rw [derivative_base, add_zero]

/-- The map preserves the scalar coordinate. -/
@[simp] theorem shearMap_fst (x : DualNumber k) : (shearMap x).fst = x.fst := rfl

/-- The infinitesimal coordinate is the prescribed sum. -/
@[simp] theorem shearMap_snd (x : DualNumber k) :
    (shearMap x).snd = derivative x.fst + x.snd := rfl

/-- Applying the shear twice is the identity in characteristic two. -/
theorem shearMap_comp : shearMap.comp shearMap = AlgHom.id Λ _ := by
  apply AlgHom.ext
  intro x
  apply TrivSqZeroExt.ext
  · rfl
  · change derivative x.fst + (derivative x.fst + x.snd) = x.snd
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add]

/-- The algebra automorphism has the same explicit map in both directions. -/
def shearEquiv : DualNumber k ≃ₐ[Λ] DualNumber k :=
  AlgEquiv.ofAlgHom shearMap shearMap shearMap_comp shearMap_comp

/-- The shear fixes the infinitesimal generator itself. -/
theorem shearMap_epsilon : shearMap (inr (1 : k)) = inr 1 := by
  apply TrivSqZeroExt.ext <;> simp

/-- The shear sends the scalar variable to `t+ε`, so it is nonidentity. -/
theorem shearMap_variable : shearMap (inl t) = inl t + inr (1 : k) := by
  apply TrivSqZeroExt.ext <;> simp

/-- The shear bundled as a morphism of the actual deformation base category. -/
def shearMorphism : dualNumber Λ k ⟶ dualNumber Λ k :=
  Hom.of shearEquiv.toAlgHom
    (isLocalHom_of_leftInverse shearEquiv.symm.toAlgHom shearEquiv.left_inv) (by
    apply AlgHom.ext
    intro x
    obtain ⟨x, rfl⟩ := residue_surjective x
    change dualNumberResidueFieldIso Λ k
      (ResidueField.mapAlgHom shearEquiv.toAlgHom (IsLocalRing.residue (DualNumber k) x)) =
        dualNumberResidueFieldIso Λ k (IsLocalRing.residue (DualNumber k) x)
    rw [ResidueField.mapAlgHom_residue, dualNumberResidueFieldIso_apply,
      dualNumberResidueFieldIso_apply]
    exact shearMap_fst x)

/-- The categorical shear squares to the identity. -/
theorem shearMorphism_comp : shearMorphism ≫ shearMorphism = 𝟙 (dualNumber Λ k) := by
  have ext_hom {f g : ArtinianLocalAlgCat.Hom (dualNumber Λ k) (dualNumber Λ k)}
      (h : f.hom = g.hom) : f = g := by
    rcases f with ⟨underlying, localHom, compatibility⟩
    rcases g with ⟨underlying', localHom', compatibility'⟩
    cases h
    rfl
  apply ext_hom
  exact shearMap_comp

/-- The actual categorical automorphism, with explicitly specified hom and inverse. -/
def shearAut : Aut (dualNumber Λ k) where
  hom := shearMorphism
  inv := shearMorphism
  hom_inv_id := shearMorphism_comp
  inv_hom_id := shearMorphism_comp

/-- The automorphism is an involution. -/
theorem shearAut_mul_self : shearAut * shearAut = 1 := by
  apply Iso.ext
  exact shearMorphism_comp

/-- The ε coefficient of the actual automorphism is one. -/
theorem epsilonScale_shearAut : epsilonScale shearAut = 1 := by
  change derivative 0 + 1 = 1
  simp

/-- Evaluation on `t` separates the automorphism from the identity. -/
theorem shearAut_ne_one : shearAut ≠ 1 := by
  intro h
  have ht := congrArg (fun g : Aut (dualNumber Λ k) ↦ (g.hom.hom (inl t)).snd) h
  change derivative t + 0 = 0 at ht
  simp at ht

/-- The two-element subgroup generated by the explicit shear involution. -/
def shearGroup : Subgroup (Aut (dualNumber Λ k)) where
  carrier := {g | g = 1 ∨ g = shearAut}
  one_mem' := Or.inl rfl
  mul_mem' := by
    rintro a b (rfl | rfl) (rfl | rfl) <;> simp [shearAut_mul_self]
  inv_mem' := by
    rintro a (rfl | rfl)
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_left shearAut_mul_self)

/-- Membership is exactly identity or the specified shear. -/
theorem mem_shearGroup (g : Aut (dualNumber Λ k)) :
    g ∈ shearGroup ↔ g = 1 ∨ g = shearAut := Iff.rfl

/-- The subgroup is finite, witnessed by its explicit two-element carrier. -/
instance shearGroup_finite : Finite shearGroup :=
  Set.Finite.to_subtype
    (show ({1, shearAut} : Set (Aut (dualNumber Λ k))).Finite by simp)

/-- The chosen involution belongs to the subgroup. -/
theorem shearAut_mem : shearAut ∈ shearGroup := Or.inr rfl

/-- The finite subgroup is nontrivial. -/
theorem shearGroup_ne_bot : shearGroup ≠ ⊥ := by
  intro h
  have hm := shearAut_mem
  rw [h] at hm
  exact shearAut_ne_one hm

/-- Every element of this nontrivial subgroup has trivial ε scaling. -/
theorem shearGroup_epsilonScale (g : shearGroup) : epsilonScale g.val = 1 := by
  rcases g.property with h | h
  · rw [h]
    rfl
  · rw [h]
    exact epsilonScale_shearAut


/-- The Frobenius shear quotient formal object has bijective differential on residue-derivation orbits. -/
theorem bijectiveDifferentialOnOrbits :
    FormalObject.BijectiveDifferentialOnOrbits (quotientFormalObject shearGroup) := sorry

/-- The Frobenius shear quotient is a predeformation category with a smooth versal
formal object and bijective differential on derivation orbits, fails Schlessinger's
condition (S2), and has tangent space bijective to the orbit classes of dual-number points. -/
theorem versal_not_schlessingerS2 :
    Functor.IsPredeformationCategory (quotientProjection shearGroup) ∧
      FormalObject.IsVersal (quotientFormalObject shearGroup) ∧
      FormalObject.BijectiveDifferentialOnOrbits (quotientFormalObject shearGroup) ∧
      ¬ Functor.HasSchlessingerS2 (quotientProjection shearGroup) ∧
      BasedFunctor.IsSmooth (quotientBasedFunctor shearGroup) ∧
      Function.Bijective (tangentSpaceMkQuot shearGroup) :=
  ⟨inferInstance, inferInstance, bijectiveDifferentialOnOrbits,
    not_hasSchlessingerS2_quotientProjection shearGroup shearGroup_ne_bot,
    inferInstance, tangentSpace_quotientBy shearGroup⟩

end ArtinianLocalAlgCat.FrobeniusShear
