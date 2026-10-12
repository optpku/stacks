/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.TensorProduct.Pi
public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.Restrict
public import ReasLib.Algebra.Homology.ShortComplex.ChangeOfRings
public import ReasLib.RingTheory.Sequence.Koszul.Homology.Zero

/-!
# Base change for first Koszul homology

The public comparison is a morphism in `ModuleCat A'`.  Restriction and extension of scalars are
kept as explicit functors, avoiding ambient module-instance diamonds.  Its construction is the
homology map of the coordinatewise comparison between the low-degree Koszul chain models.

@stack 063Q
-/

@[expose] public section

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits
open Algebra.TensorProduct
open scoped TensorProduct

namespace KoszulComplex.Homology.H1.BaseChange

variable {A B A' : Type u} [CommRing A] [CommRing B] [CommRing A']
variable [Algebra A B] [Algebra A A'] {n : ℕ}

/-- The image of a finite family in the tensor-product ring `A' ⊗[A] B`. -/
@[stacks 063Q "base-changed Koszul family"]
abbrev family (f : Fin n → B) : Fin n → A' ⊗[A] B :=
  fun i ↦ includeRight (f i)

/-- First Koszul homology over `B`, explicitly restricted to an `A`-module object. -/
@[stacks 063Q "restricted source first Koszul homology"]
abbrev sourceObj (f : Fin n → B) : ModuleCat A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj
    (KoszulComplex.Homology.H1.obj f B)

/-- Zeroth Koszul homology over `B`, explicitly restricted to an `A`-module object. -/
@[stacks 063Q "restricted source zeroth Koszul homology"]
abbrev sourceH0 (f : Fin n → B) : ModuleCat A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj
    (KoszulComplex.Homology.H0.obj f B)

/-- Restriction of scalars carries the regular-coefficient zeroth-homology presentation to an
`A`-linear identification with the quotient by the generated ideal. -/
@[stacks 063Q "restricted zeroth Koszul homology presentation"]
noncomputable def sourceH0Iso (f : Fin n → B) :
    sourceH0 (A := A) f ≅
      (ModuleCat.restrictScalars (algebraMap A B)).obj
        (ModuleCat.of B (B ⧸ Ideal.span (Set.range f))) :=
  (ModuleCat.restrictScalars (algebraMap A B)).mapIso
    (KoszulComplex.Homology.H0.presentationIso f)

/-- Flatness of restricted zeroth Koszul homology is equivalent to flatness of its quotient
presentation. -/
theorem sourceH0_flat_iff (f : Fin n → B) :
    Module.Flat A (sourceH0 (A := A) f) ↔
      Module.Flat A (B ⧸ Ideal.span (Set.range f)) := sorry

/-- Flatness of the quotient presentation is available automatically on the restricted zeroth
Koszul homology owner. -/
@[stacks 063Q "flatness of restricted zeroth Koszul homology"]
instance sourceH0Flat (f : Fin n → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))] :
    Module.Flat A (sourceH0 (A := A) f) := sorry

/-- First Koszul homology after tensor base change, explicitly restricted from the tensor-product
ring to an `A'`-module object. -/
@[stacks 063Q "target first Koszul homology after tensor base change"]
abbrev targetObj (f : Fin n → B) : ModuleCat A' :=
  (ModuleCat.restrictScalars (algebraMap A' (A' ⊗[A] B))).obj
    (KoszulComplex.Homology.H1.obj (family (A := A) (A' := A') f) (A' ⊗[A] B))

/-- The source low-degree Koszul model after restriction of scalars from `B` to `A`. -/
@[stacks 063Q "restricted source low-degree Koszul model"]
abbrev sourceModel (f : Fin n → B) : ShortComplex (ModuleCat A) :=
  (KoszulComplex.Homology.H1.model f B).map
    (ModuleCat.restrictScalars (algebraMap A B))

/-- The quotient-flat hypothesis supplies the concrete outgoing-cokernel flatness expected by
the generic short-complex homology comparison. -/
@[stacks 063Q "flat outgoing cokernel of the restricted Koszul model"]
instance sourceOutgoingCokernelFlat (f : Fin n → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))] :
    Module.Flat A
      (ModuleCat.ExtendScalars.HomologyComparison.outgoingCokernel
        (sourceModel (A := A) f)) := sorry

/-- The target low-degree Koszul model after restriction first to `A'` and then to `A`. -/
@[stacks 063Q "restricted target low-degree Koszul model"]
abbrev targetModel (f : Fin n → B) : ShortComplex (ModuleCat A) :=
  ((KoszulComplex.Homology.H1.model (family (A := A) (A' := A') f) (A' ⊗[A] B)).map
      (ModuleCat.restrictScalars (algebraMap A' (A' ⊗[A] B)))).map
    (ModuleCat.restrictScalars (algebraMap A A'))

/-- A power of the regular `B`-module, restricted to `A`. -/
@[stacks 063Q "restricted source power for Koszul base change"]
abbrev sourcePower (ι : Type v) : ModuleCat.{max u v} A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B (ι → B))

/-- A power of the tensor-product ring, restricted directly along
`A → A' ⊗[A] B`. -/
@[stacks 063Q "directly restricted target power for Koszul base change"]
abbrev directTargetPower (ι : Type v) : ModuleCat.{max u v} A :=
  (ModuleCat.restrictScalars (algebraMap A (A' ⊗[A] B))).obj
    (ModuleCat.of (A' ⊗[A] B) (ι → A' ⊗[A] B))

/-- A power of the tensor-product ring, restricted along `A → A' → A' ⊗[A] B`. -/
@[stacks 063Q "successively restricted target power for Koszul base change"]
abbrev targetPower (ι : Type v) : ModuleCat.{max u v} A :=
  (ModuleCat.restrictScalars (algebraMap A A')).obj
    ((ModuleCat.restrictScalars (algebraMap A' (A' ⊗[A] B))).obj
      (ModuleCat.of (A' ⊗[A] B) (ι → A' ⊗[A] B)))

/-- Direct and successive restriction of a tensor-product power are canonically isomorphic. -/
@[stacks 063Q "comparison of direct and successive restriction on powers"]
def targetPowerIso (ι : Type v) :
    directTargetPower (A := A) (B := B) (A' := A') ι ≅
      targetPower (A := A) (B := B) (A' := A') ι :=
  ModuleCat.restrictScalarsComp'App
    (algebraMap A A') (algebraMap A' (A' ⊗[A] B))
    (algebraMap A (A' ⊗[A] B))
    (IsScalarTower.algebraMap_eq A A' (A' ⊗[A] B))
    (ModuleCat.of (A' ⊗[A] B) (ι → A' ⊗[A] B))

/-- Coordinatewise application of the canonical map `B → A' ⊗[A] B` on the canonical
`A`-module structures. -/
@[stacks 063Q "coordinatewise tensor-product base-change map"]
def canonicalPiLinearMap (ι : Type v) :
    (ι → B) →ₗ[A] (ι → A' ⊗[A] B) :=
  LinearMap.pi fun i ↦
    (includeRight (R := A) (A := A') (B := B)).toLinearMap.comp
      (LinearMap.proj (R := A) (φ := fun _ : ι ↦ B) i)

/-- Coordinatewise application of `B → A' ⊗[A] B`, viewed between the explicit restricted-scalar
module objects. -/
@[stacks 063Q "coordinatewise map between restricted powers"]
def piMap (ι : Type v) :
    sourcePower (A := A) (B := B) ι ⟶ targetPower (A := A) (B := B) (A' := A') ι :=
  (ModuleCat.RestrictScalars.identityIso (R := A) (S := B) (ι → B)).hom ≫
    ModuleCat.ofHom (canonicalPiLinearMap (A := A) (B := B) (A' := A') ι) ≫
      (ModuleCat.RestrictScalars.identityIso
        (R := A) (S := A' ⊗[A] B) (ι → A' ⊗[A] B)).inv ≫
        (targetPowerIso (A := A) (B := B) (A' := A') ι).hom

/-- The regular `B`-module restricted to `A`. -/
@[stacks 063Q "restricted source regular module"]
abbrev sourceRing : ModuleCat A :=
  (ModuleCat.restrictScalars (algebraMap A B)).obj (ModuleCat.of B B)

/-- The tensor-product ring restricted directly along `A → A' ⊗[A] B`. -/
@[stacks 063Q "directly restricted target regular module"]
abbrev directTargetRing : ModuleCat A :=
  (ModuleCat.restrictScalars (algebraMap A (A' ⊗[A] B))).obj
    (ModuleCat.of (A' ⊗[A] B) (A' ⊗[A] B))

/-- The tensor-product ring restricted along `A → A' → A' ⊗[A] B`. -/
@[stacks 063Q "successively restricted target regular module"]
abbrev targetRing : ModuleCat A :=
  (ModuleCat.restrictScalars (algebraMap A A')).obj
    ((ModuleCat.restrictScalars (algebraMap A' (A' ⊗[A] B))).obj
      (ModuleCat.of (A' ⊗[A] B) (A' ⊗[A] B)))

/-- Direct and successive restriction of the tensor-product ring are canonically isomorphic. -/
@[stacks 063Q "comparison of direct and successive restriction on regular modules"]
def targetRingIso :
    directTargetRing (A := A) (B := B) (A' := A') ≅
      targetRing (A := A) (B := B) (A' := A') :=
  ModuleCat.restrictScalarsComp'App
    (algebraMap A A') (algebraMap A' (A' ⊗[A] B))
    (algebraMap A (A' ⊗[A] B))
    (IsScalarTower.algebraMap_eq A A' (A' ⊗[A] B))
    (ModuleCat.of (A' ⊗[A] B) (A' ⊗[A] B))

/-- The canonical map `B → A' ⊗[A] B` on the canonical `A`-module structures. -/
@[stacks 063Q "canonical tensor-product ring map as a linear map"]
def canonicalRingLinearMap : B →ₗ[A] A' ⊗[A] B :=
  (includeRight (R := A) (A := A') (B := B)).toLinearMap

/-- The canonical map `B → A' ⊗[A] B`, viewed between the scalar-restricted regular modules. -/
@[stacks 063Q "canonical map between restricted regular modules"]
def ringMap : sourceRing (A := A) (B := B) ⟶ targetRing (A := A) (B := B) (A' := A') :=
  (ModuleCat.RestrictScalars.identityIso (R := A) (S := B) B).hom ≫
    ModuleCat.ofHom (canonicalRingLinearMap (A := A) (B := B) (A' := A')) ≫
      (ModuleCat.RestrictScalars.identityIso
        (R := A) (S := A' ⊗[A] B) (A' ⊗[A] B)).inv ≫
        (targetRingIso (A := A) (B := B) (A' := A')).hom

/-- Coordinatewise base change commutes with the trivial-relation boundary. -/
theorem relationBoundary_naturality (f : Fin n → B) :
    piMap (A := A) (A' := A') (Fin n × Fin n) ≫
        (targetModel (A := A) (A' := A') f).f =
      (sourceModel (A := A) f).f ≫ piMap (A := A) (A' := A') (Fin n) := sorry

/-- Coordinatewise base change commutes with the finite-family linear-combination map. -/
theorem linearCombination_naturality (f : Fin n → B) :
    piMap (A := A) (A' := A') (Fin n) ≫
        (targetModel (A := A) (A' := A') f).g =
      (sourceModel (A := A) f).g ≫ ringMap (A := A) (A' := A') := sorry

/-- The morphism of low-degree Koszul chain models induced by tensor base change. -/
@[stacks 063Q "map of low-degree Koszul models under base change"]
def modelMap (f : Fin n → B) :
    sourceModel (A := A) f ⟶ targetModel (A := A) (A' := A') f :=
  ShortComplex.Hom.mk
    (piMap (A := A) (A' := A') (Fin n × Fin n))
    (piMap (A := A) (A' := A') (Fin n))
    (ringMap (A := A) (A' := A'))
    (relationBoundary_naturality (A := A) (A' := A') f)
    (linearCombination_naturality (A := A) (A' := A') f)

/-- Restriction of scalars identifies source-model homology with the restricted source owner. -/
@[stacks 063Q "source homology comparison for the low-degree Koszul model"]
noncomputable def sourceHomologyIso (f : Fin n → B) :
    (sourceModel (A := A) f).homology ≅ sourceObj (A := A) f :=
  ModuleCat.restrictScalarsShortComplexHomologyIso
    (algebraMap A B) (KoszulComplex.Homology.H1.model f B)

/-- Iterated restriction of scalars identifies target-model homology with the restricted target
owner. -/
@[stacks 063Q "target homology comparison for the low-degree Koszul model"]
noncomputable def targetHomologyIso (f : Fin n → B) :
    (targetModel (A := A) (A' := A') f).homology ≅
      (ModuleCat.restrictScalars (algebraMap A A')).obj
        (targetObj (A := A) (A' := A') f) :=
  ModuleCat.restrictScalarsShortComplexHomologyIso (algebraMap A A')
      ((KoszulComplex.Homology.H1.model (family (A := A) (A' := A') f)
        (A' ⊗[A] B)).map
          (ModuleCat.restrictScalars (algebraMap A' (A' ⊗[A] B)))) ≪≫
    (ModuleCat.restrictScalars (algebraMap A A')).mapIso
      (ModuleCat.restrictScalarsShortComplexHomologyIso
        (algebraMap A' (A' ⊗[A] B))
        (KoszulComplex.Homology.H1.model (family (A := A) (A' := A') f)
          (A' ⊗[A] B)))

/-- The adjoint `A`-linear comparison before extension of scalars. -/
@[stacks 063Q "adjoint form of the first Koszul homology base-change map"]
noncomputable def restrictedMap (f : Fin n → B) :
    sourceObj (A := A) f ⟶
      (ModuleCat.restrictScalars (algebraMap A A')).obj
        (targetObj (A := A) (A' := A') f) :=
  (sourceHomologyIso (A := A) f).inv ≫
    ShortComplex.homologyMap (modelMap (A := A) (A' := A') f) ≫
      (targetHomologyIso (A := A) (A' := A') f).hom

/-- The comparison between the explicit low-degree first-homology
models before and after tensor base change. -/
@[stacks 063Q "low-degree base-change map on first Koszul homology"]
noncomputable def map (f : Fin n → B) :
    (ModuleCat.extendScalars (algebraMap A A')).obj (sourceObj (A := A) f) ⟶
      targetObj (A := A) (A' := A') f :=
  ((ModuleCat.extendRestrictScalarsAdj (algebraMap A A')).homEquiv _ _).symm
    (restrictedMap (A := A) (A' := A') f)

/-- Under the extension-restriction adjunction, the base-change comparison is exactly the
restricted low-degree homology map used to construct it. -/
theorem map_adjunct (f : Fin n → B) :
    (ModuleCat.extendRestrictScalarsAdj (algebraMap A A')).homEquiv _ _
        (map (A := A) (A' := A') f) =
      restrictedMap (A := A) (A' := A') f := sorry

/-- The first-Koszul-homology base-change comparison is surjective when zeroth homology is flat
over the base ring. -/
theorem map_surjective_of_h0_flat (f : Fin n → B)
    [Module.Flat A (sourceH0 (A := A) f)] :
    Function.Surjective (map (A := A) (A' := A') f) := sorry

/-- The first-Koszul-homology base-change comparison is surjective
when the quotient by the generated ideal is flat over the base ring. -/
@[stacks 063Q "surjectivity of first Koszul homology under base change"]
theorem map_surjective (f : Fin n → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))] :
    Function.Surjective (map (A := A) (A' := A') f) := sorry

/-- Under the flat-quotient hypothesis, the first-Koszul-homology base-change comparison is an
epimorphism in `ModuleCat A'`. -/
@[stacks 063Q "first Koszul homology base-change map is epi"]
instance map_epi (f : Fin n → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))] :
    Epi (map (A := A) (A' := A') f) := sorry

/-- Under the flat-quotient hypothesis, vanishing of source first homology implies vanishing after
arbitrary tensor base change. -/
theorem target_isZero_of_source_isZero (f : Fin n → B)
    [Module.Flat A (B ⧸ Ideal.span (Set.range f))]
    (h : IsZero (sourceObj (A := A) f)) :
    IsZero (targetObj (A := A) (A' := A') f) := sorry

end KoszulComplex.Homology.H1.BaseChange
