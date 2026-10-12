/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Localization.Opposite
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.Derived
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.InternalHom.Derived.Bifunctor
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorHom.Derived.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Bimodule.TensorProduct.Derived.Unit.Naturality
public import ReasLib.Algebra.Homology.DifferentialGradedModule.Derived.Homology.Representable
public import ReasLib.Algebra.Category.ModuleCat.Ulift
public import ReasLib.CategoryTheory.Shift.ShiftedHom.Adjunction.Functor

/-!
# Cohomology of derived internal Hom

For a differential graded `(A, B)`-bimodule `T`, cohomology of derived fixed-source internal
Hom is represented by the underlying right derived object of `T`.  The main API is natural in
the derived target and contravariantly natural in `T`; no resolution or K-injectivity choice is
part of its public surface.  The current regular-object tensor-unit owner requires the left
module carrier of `T` to agree with the carrier of `A`; the right algebra carrier remains
independent.  Thus this leaf supports `A : CochainDGAlgebra.{u, w} R`,
`B : CochainDGAlgebra.{u, x} R`, and
`T : DifferentialGradedBimodule.{u, w, w, x} A B`.  The preceding internal-Hom and tensor
owners already keep the two algebra-carrier universes independent; lifting the module carrier
itself requires a strict and derived bimodule-`ULift` compatibility layer.
-/

@[expose] public section

noncomputable section

universe u w x

open CategoryTheory DifferentialGradedCategory Opposite
open scoped DifferentialGradedCategory DifferentialGradedModule

namespace DifferentialGradedBimodule.InternalHom.Derived.Cohomology

variable {R : Type u} [CommRing R]
variable {A : CochainDGAlgebra.{u, w} R} {B : CochainDGAlgebra.{u, x} R}

/-! The target module universe is the least common universe
`max (max u (w + 1)) x`: homology first lifts through `A`, then the module carrier is lifted
once more to match the right-derived `B`-category. -/
/-- Lifted degree-`n` cohomology of derived fixed-source internal Hom. -/
@[stacks 0CS5 "universe-lifted fixed-source cohomology functor"]
def uliftFunctor (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    DifferentialGradedModule.Derived.Category.{u, w, x} B ⥤
      ModuleCat.{max (max u (w + 1)) x} R :=
  InternalHom.derivedFunctor T ⋙
    DifferentialGradedModule.Derived.Homology.uliftFunctor A n ⋙
      ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R

/-- Shifted derived Hom from the underlying right derived object of a bimodule. -/
@[stacks 0CS5 "fixed-source shifted Hom functor"]
def shiftedHomFunctor (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    DifferentialGradedModule.Derived.Category.{u, w, x} B ⥤
      ModuleCat.{max (max u (w + 1)) x} R :=
  ShiftedHom.targetFunctor.{u, max (max u (w + 1)) x, max (max u (w + 1)) x}
    R T.rightDerivedObject n

/-- Lifted cohomology of fixed-source derived internal Hom is additive in the derived target. -/
@[stacks 0CS5 "additivity of fixed-source derived internal-Hom cohomology"]
noncomputable instance uliftFunctorAdditive (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (n : ℤ) :
    (uliftFunctor T n).Additive := sorry

/-- Lifted cohomology of fixed-source derived internal Hom is `R`-linear in the derived target. -/
@[stacks 0CS5 "linearity of fixed-source derived internal-Hom cohomology"]
noncomputable instance uliftFunctorLinear (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (n : ℤ) :
    Functor.Linear R (uliftFunctor T n) := sorry

/-- Shifted Hom from the underlying right derived object is additive in its target. -/
@[stacks 0CS5 "additivity of fixed-source shifted derived Hom"]
noncomputable instance shiftedHomFunctorAdditive (
    T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    (shiftedHomFunctor T n).Additive := sorry

/-- Shifted Hom from the underlying right derived object is `R`-linear in its target. -/
@[stacks 0CS5 "linearity of fixed-source shifted derived Hom"]
noncomputable instance shiftedHomFunctorLinear (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (n : ℤ) :
    Functor.Linear R (shiftedHomFunctor T n) := sorry

/-! The comparison is assembled from three canonical library isomorphisms. -/

/-- Lift the derived homology representability isomorphism to the common module universe. -/
@[stacks 0CS5 "lifted representability transport for derived internal Hom"]
noncomputable def representableUliftIso
    (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    (InternalHom.derivedFunctor T ⋙
      DifferentialGradedModule.Derived.Homology.uliftFunctor A n) ⋙
        ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R ≅
      (InternalHom.derivedFunctor T ⋙
        DifferentialGradedModule.Derived.Homology.representedFunctor A n) ⋙
          ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R :=
  Functor.isoWhiskerRight
    (Functor.isoWhiskerLeft (InternalHom.derivedFunctor T)
      (DifferentialGradedModule.Derived.Homology.representableIso A n))
    (ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R)

/-- Move the shifted-Hom adjunction comparison to the common module universe. -/
@[stacks 0CS5 "lifted shifted-Hom adjunction transport"]
noncomputable def adjunctionUliftIso
    (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    (InternalHom.derivedFunctor T ⋙
      ShiftedHom.targetFunctor R (DifferentialGradedModule.Derived.regularObject A) n) ⋙
        ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R ≅
      ShiftedHom.targetFunctor R
          ((Tensor.derivedFunctor T).obj (DifferentialGradedModule.Derived.regularObject A)) n ⋙
        ModuleCat.uliftFunctor.{max u (w + 1), max (max u (w + 1)) x} R :=
  (DifferentialGradedBimodule.TensorHom.derivedAdjunction T).uliftTargetFunctorIso
    (DifferentialGradedModule.Derived.regularObject A) n

/-- Transport the tensor representative to the underlying right-derived object and collapse the
redundant target lift. -/
@[stacks 0CS5 "regular-object transport for lifted shifted Hom"]
noncomputable def regularObjectUliftIso
    (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    ShiftedHom.targetFunctor R
          ((Tensor.derivedFunctor T).obj (DifferentialGradedModule.Derived.regularObject A)) n ⋙
        ModuleCat.uliftFunctor.{max u (w + 1), max (max u (w + 1)) x} R ≅
      shiftedHomFunctor T n :=
  Functor.isoWhiskerRight
      (ShiftedHom.targetIso.{u, max (max u (w + 1)) x, max (max u (w + 1)) x}
        R (Tensor.regularObjectIso T) n)
      (ModuleCat.uliftFunctor.{max u (w + 1), max (max u (w + 1)) x} R) ≪≫
    Functor.isoWhiskerLeft (shiftedHomFunctor T n)
      (ModuleCat.uliftFunctorTrivial.{u, max (max u (w + 1)) x, max u (w + 1)} (R := R)) ≪≫
      (shiftedHomFunctor T n).rightUnitor

/-- Lemma 22.31.4 (0CS5), in resolution-independent form: degree-`n` cohomology of
`RHom(T, -)` is naturally shifted derived Hom from the underlying right derived object of `T`.
The comparison is assembled from representability, adjunction, and tensor-unit transport. -/
@[stacks 0CS5 "derived internal-Hom cohomology as shifted derived Hom"]
noncomputable def uliftIso
    (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    uliftFunctor T n ≅ shiftedHomFunctor T n :=
  representableUliftIso T n ≪≫ adjunctionUliftIso T n ≪≫ regularObjectUliftIso T n

/-- The canonical linear comparison from derived internal-Hom cohomology to shifted derived
Hom. -/
@[stacks 0CS5 "pointwise lifted cohomology comparison map"]
noncomputable def uliftLinearMap (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ) :
    (uliftFunctor T n).obj M →ₗ[R] (shiftedHomFunctor T n).obj M :=
  ((uliftIso T n).app M).toLinearEquiv.toLinearMap

/-- Move shifted derived Hom back through the tensor-Hom adjunction and then apply the inverse
homology representability comparison. -/
@[stacks 0CS5 "pointwise inverse lifted cohomology comparison map"]
noncomputable def uliftInverseLinearMap
    (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ) :
    (shiftedHomFunctor T n).obj M →ₗ[R] (uliftFunctor T n).obj M :=
  ((uliftIso T n).app M).toLinearEquiv.symm.toLinearMap

/-- Lifted derived internal-Hom cohomology is linearly equivalent to shifted derived Hom from
the underlying right derived object, obtained from the canonical natural isomorphism. -/
@[stacks 0CS5 "pointwise lifted cohomology comparison equivalence"]
noncomputable def uliftLinearEquiv (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ) :
    (uliftFunctor T n).obj M ≃ₗ[R] (shiftedHomFunctor T n).obj M :=
  ((uliftIso T n).app M).toLinearEquiv

/-- The canonical derived internal-Hom cohomology comparison is bijective, as a consequence
of the explicit linear equivalence. -/
@[stacks 0CS5 "bijectivity of the lifted cohomology comparison"]
theorem uliftLinearMap_bijective (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ) :
    Function.Bijective (uliftLinearMap T M n) := sorry

/-- The forward map of `uliftLinearEquiv` is the canonical comparison map. -/
@[simp, stacks 0CS5 "forward lifted cohomology comparison formula"]
theorem uliftLinearEquiv_apply (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ)
    (x : (uliftFunctor T n).obj M) :
    uliftLinearEquiv T M n x = uliftLinearMap T M n x := sorry

/-- The inverse map of `uliftLinearEquiv` is the explicit currying comparison. -/
@[simp, stacks 0CS5 "inverse lifted cohomology comparison formula"]
theorem uliftLinearEquiv_symm_apply (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ)
    (y : (shiftedHomFunctor T n).obj M) :
    (uliftLinearEquiv T M n).symm y = uliftInverseLinearMap T M n y := sorry

/-- The canonical linear bridge from ordinary derived internal-Hom cohomology to the
universe-lifted cohomology functor.  It encapsulates the two successive module lifts needed to
reach the common target universe. -/
@[stacks 0CS5 "ordinary-to-lifted derived internal-Hom cohomology"]
noncomputable def homologyUliftEquiv
    (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ) :
    (DifferentialGradedModule.Derived.homologyFunctor A n).obj
        ((InternalHom.derivedFunctor T).obj M) ≃ₗ[R]
      (uliftFunctor T n).obj M :=
  (ULift.moduleEquiv (R := R)
      (M := (DifferentialGradedModule.Derived.homologyFunctor A n).obj
        ((InternalHom.derivedFunctor T).obj M))).symm.trans
    (ULift.moduleEquiv (R := R)
      (M := (DifferentialGradedModule.Derived.Homology.uliftFunctor A n).obj
        ((InternalHom.derivedFunctor T).obj M))).symm

/-- The forward ordinary-to-lifted bridge applies the two canonical universe lifts. -/
@[simp, stacks 0CS5 "formula for the ordinary-to-lifted cohomology bridge"]
theorem homologyUliftEquiv_apply
    (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ)
    (x : (DifferentialGradedModule.Derived.homologyFunctor A n).obj
      ((InternalHom.derivedFunctor T).obj M)) :
    homologyUliftEquiv T M n x = ULift.up (ULift.up x) := sorry

/-- The inverse ordinary-to-lifted bridge removes both canonical universe lifts. -/
@[simp, stacks 0CS5 "inverse formula for the ordinary-to-lifted cohomology bridge"]
theorem homologyUliftEquiv_symm_apply
    (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ)
    (x : (uliftFunctor T n).obj M) :
    (homologyUliftEquiv T M n).symm x = x.down.down := sorry

/-- Ordinary derived internal-Hom cohomology is linearly equivalent to shifted derived Hom;
this pointwise API hides the universe lift used by the functorial comparison. -/
@[stacks 0CS5 "derived internal-Hom cohomology as ordinary shifted Hom"]
noncomputable def linearEquiv (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ) :
    (DifferentialGradedModule.Derived.homologyFunctor A n).obj
        ((InternalHom.derivedFunctor T).obj M) ≃ₗ[R]
      (shiftedHomFunctor T n).obj M :=
  (homologyUliftEquiv T M n).trans (uliftLinearEquiv T M n)

/-- The ordinary comparison is the lifted comparison applied to `ULift.up x`. -/
@[simp, stacks 0CS5 "ordinary cohomology comparison formula"]
theorem linearEquiv_apply (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ)
    (x : (DifferentialGradedModule.Derived.homologyFunctor A n).obj
      ((InternalHom.derivedFunctor T).obj M)) :
    linearEquiv T M n x =
      uliftLinearMap T M n (homologyUliftEquiv T M n x) := sorry

/-- The inverse ordinary comparison removes the universe lift from the explicit inverse. -/
@[simp, stacks 0CS5 "inverse ordinary cohomology comparison formula"]
theorem linearEquiv_symm_apply (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ)
    (y : (shiftedHomFunctor T n).obj M) :
    (linearEquiv T M n).symm y =
      (homologyUliftEquiv T M n).symm (uliftInverseLinearMap T M n y) := sorry

/-- The ordinary comparison is natural in its derived target. -/
@[stacks 0CS5 "target naturality of ordinary cohomology comparison"]
theorem linearEquiv_naturality_target
    (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    {M N : DifferentialGradedModule.Derived.Category.{u, w, x} B} (f : M ⟶ N)
    (n : ℤ)
    (x : (DifferentialGradedModule.Derived.homologyFunctor A n).obj
      ((InternalHom.derivedFunctor T).obj M)) :
    linearEquiv T N n
        (ModuleCat.Hom.hom
          ((DifferentialGradedModule.Derived.homologyFunctor A n).map
            ((InternalHom.derivedFunctor T).map f)) x) =
      ModuleCat.Hom.hom ((shiftedHomFunctor T n).map f)
        (linearEquiv T M n x) := sorry

/-- A bimodule morphism acts contravariantly on derived internal-Hom cohomology. -/
@[stacks 0CS5 "contravariant lifted cohomology map"]
def uliftSourceMap {T T' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : T ⟶ T')
    (n : ℤ) : uliftFunctor T' n ⟶ uliftFunctor T n :=
  Functor.whiskerRight (InternalHom.derivedNatTrans f)
    (DifferentialGradedModule.Derived.Homology.uliftFunctor A n ⋙
      ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R)

/-- A bimodule morphism acts contravariantly on shifted Hom through its underlying right
derived morphism. -/
@[stacks 0CS5 "contravariant shifted-Hom map"]
def shiftedHomMap {T T' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : T ⟶ T')
    (n : ℤ) : shiftedHomFunctor T' n ⟶ shiftedHomFunctor T n :=
  ShiftedHom.targetMap.{u, max (max u (w + 1)) x, max (max u (w + 1)) x} R
    ((DifferentialGradedBimodule.rightDerivedObjectFunctor A B).map f) n

/-- The identity bimodule morphism acts trivially on lifted cohomology functors. -/
@[simp, stacks 0CS5 "identity of lifted cohomology source maps"]
theorem uliftSourceMap_id (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    uliftSourceMap (𝟙 T) n = 𝟙 (uliftFunctor T n) := sorry

/-- Contravariance reverses composition on lifted cohomology functors. -/
@[simp, stacks 0CS5 "composition of lifted cohomology source maps"]
theorem uliftSourceMap_comp
    {T T' T'' : DifferentialGradedBimodule.{u, w, w, x} A B}
    (f : T ⟶ T') (g : T' ⟶ T'') (n : ℤ) :
    uliftSourceMap (f ≫ g) n = uliftSourceMap g n ≫ uliftSourceMap f n := sorry

/-- The identity bimodule morphism acts trivially on shifted-Hom functors. -/
@[simp, stacks 0CS5 "identity of shifted-Hom source maps"]
theorem shiftedHomMap_id (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    shiftedHomMap (𝟙 T) n = 𝟙 (shiftedHomFunctor T n) := sorry

/-- Contravariance reverses composition on shifted-Hom functors. -/
@[simp, stacks 0CS5 "composition of shifted-Hom source maps"]
theorem shiftedHomMap_comp
    {T T' T'' : DifferentialGradedBimodule.{u, w, w, x} A B}
    (f : T ⟶ T') (g : T' ⟶ T'') (n : ℤ) :
    shiftedHomMap (f ≫ g) n = shiftedHomMap g n ≫ shiftedHomMap f n := sorry

/-- Derived internal-Hom cohomology sends a bimodule quasi-isomorphism to an isomorphism of
target functors. -/
@[stacks 0CS5 "quasi-isomorphisms induce lifted cohomology isomorphisms"]
theorem uliftSourceMap_isIso_of_quasiIso
    {T T' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : T ⟶ T')
    (n : ℤ) (hf : DifferentialGradedBimodule.quasiIso A B f) :
    IsIso (uliftSourceMap f n) := sorry

/-- Shifted Hom from the underlying right derived object sends a bimodule quasi-isomorphism
to an isomorphism of target functors. -/
@[stacks 0CS5 "quasi-isomorphisms induce shifted-Hom isomorphisms"]
theorem shiftedHomMap_isIso_of_quasiIso
    {T T' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : T ⟶ T')
    (n : ℤ) (hf : DifferentialGradedBimodule.quasiIso A B f) :
    IsIso (shiftedHomMap f n) := sorry

/-- The fixed-bimodule comparison is contravariantly natural in the bimodule source. -/
@[reassoc, stacks 0CS5 "source naturality of lifted cohomology comparison"]
theorem uliftIso_naturality_source
    {T T' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : T ⟶ T') (n : ℤ) :
    uliftSourceMap f n ≫ (uliftIso T n).hom =
      (uliftIso T' n).hom ≫ shiftedHomMap f n := sorry

/-- The fixed-bimodule comparison is natural in its derived target.  This is the equation
`(uliftIso T n).hom.naturality f`, exposed at the owner level for direct rewriting. -/
@[reassoc, stacks 0CS5 "target naturality of the lifted cohomology comparison"]
theorem uliftIso_naturality_target
    (T : DifferentialGradedBimodule.{u, w, w, x} A B)
    {M N : DifferentialGradedModule.Derived.Category.{u, w, x} B} (f : M ⟶ N) (n : ℤ) :
    (uliftFunctor T n).map f ≫ (uliftIso T n).hom.app N =
      (uliftIso T n).hom.app M ≫ (shiftedHomFunctor T n).map f := sorry

/-- The ordinary comparison is contravariantly natural in its bimodule source. -/
@[stacks 0CS5 "source naturality of ordinary cohomology comparison"]
theorem linearEquiv_naturality_source
    {T T' : DifferentialGradedBimodule.{u, w, w, x} A B} (f : T ⟶ T')
    (M : DifferentialGradedModule.Derived.Category.{u, w, x} B) (n : ℤ)
    (x : (DifferentialGradedModule.Derived.homologyFunctor A n).obj
      ((InternalHom.derivedFunctor T').obj M)) :
    linearEquiv T M n
        (ModuleCat.Hom.hom
          ((DifferentialGradedModule.Derived.homologyFunctor A n).map
            ((InternalHom.derivedNatTrans f).app M)) x) =
      ModuleCat.Hom.hom ((shiftedHomMap f n).app M)
        (linearEquiv T' M n x) := sorry

/-- Lifted derived internal-Hom cohomology on the opposite category of strict bimodules. -/
@[stacks 0CS5 "strict-source derived internal-Hom cohomology bifunctor"]
def uliftSourceBifunctor (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ ⥤
      (DifferentialGradedModule.Derived.Category.{u, w, x} B ⥤
        ModuleCat.{max (max u (w + 1)) x} R) :=
  InternalHom.derivedBimoduleFunctor A B ⋙
    (Functor.whiskeringRight _ _ _).obj
      (DifferentialGradedModule.Derived.Homology.uliftFunctor A n ⋙
        ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R)

/-- Shifted derived Hom on the opposite category of strict bimodules. -/
@[stacks 0CS5 "strict-source shifted-Hom bifunctor"]
def shiftedHomSourceBifunctor (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ ⥤
      (DifferentialGradedModule.Derived.Category.{u, w, x} B ⥤
        ModuleCat.{max (max u (w + 1)) x} R) :=
  (DifferentialGradedBimodule.rightDerivedObjectFunctor A B).op ⋙
    ShiftedHom.linearCoyoneda R (DifferentialGradedModule.Derived.Category B) n

/-- The strict-source cohomology bifunctor is additive in the bimodule variable. -/
@[stacks 0CS5 "additivity of strict-source derived internal-Hom cohomology"]
noncomputable instance uliftSourceBifunctorAdditive (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (uliftSourceBifunctor A B n).Additive := sorry

/-- The strict-source cohomology bifunctor is `R`-linear in the bimodule variable. -/
@[stacks 0CS5 "linearity of strict-source derived internal-Hom cohomology"]
noncomputable instance uliftSourceBifunctorLinear (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    Functor.Linear R (uliftSourceBifunctor A B n) := sorry

/-- The strict-source shifted-Hom bifunctor is additive in the bimodule variable. -/
@[stacks 0CS5 "additivity of strict-source shifted Hom"]
noncomputable instance shiftedHomSourceBifunctorAdditive (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (shiftedHomSourceBifunctor A B n).Additive := sorry

/-- The strict-source shifted-Hom bifunctor is `R`-linear in the bimodule variable. -/
@[stacks 0CS5 "linearity of strict-source shifted Hom"]
noncomputable instance shiftedHomSourceBifunctorLinear (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    Functor.Linear R (shiftedHomSourceBifunctor A B n) := sorry

/-- Evaluating the cohomology bifunctor at a bimodule recovers its fixed-source functor. -/
@[simp, stacks 0CS5 "strict-object formula for the lifted cohomology bifunctor"]
theorem uliftSourceBifunctor_obj (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ)
    (T : (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ) :
    (uliftSourceBifunctor A B n).obj T = uliftFunctor T.unop n := sorry

/-- The bimodule action of the cohomology bifunctor is derived precomposition. -/
@[simp, stacks 0CS5 "strict-morphism formula for the lifted cohomology bifunctor"]
theorem uliftSourceBifunctor_map (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ)
    {T T' : (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ} (f : T ⟶ T') :
    (uliftSourceBifunctor A B n).map f = uliftSourceMap f.unop n := sorry

/-- Evaluating the shifted-Hom bifunctor at a bimodule recovers shifted Hom from its underlying
right derived object. -/
@[simp, stacks 0CS5 "strict-object formula for the shifted-Hom bifunctor"]
theorem shiftedHomSourceBifunctor_obj (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ)
    (T : (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ) :
    (shiftedHomSourceBifunctor A B n).obj T = shiftedHomFunctor T.unop n := sorry

/-- The bimodule action of the shifted-Hom bifunctor is precomposition by the underlying right
derived morphism. -/
@[simp, stacks 0CS5 "strict-morphism formula for the shifted-Hom bifunctor"]
theorem shiftedHomSourceBifunctor_map (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ)
    {T T' : (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ} (f : T ⟶ T') :
    (shiftedHomSourceBifunctor A B n).map f = shiftedHomMap f.unop n := sorry

/-- The cohomology bifunctor inverts bimodule quasi-isomorphisms in its contravariant
variable. -/
@[stacks 0CS5 "strict cohomology bifunctor inverts quasi-isomorphisms"]
theorem uliftSourceBifunctor_map_isIso_of_quasiIso
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ)
    {T T' : (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ} (f : T ⟶ T')
    (hf : DifferentialGradedBimodule.quasiIso A B f.unop) :
    IsIso ((uliftSourceBifunctor A B n).map f) := sorry

/-- The shifted-Hom bifunctor inverts bimodule quasi-isomorphisms in its contravariant
variable. -/
@[stacks 0CS5 "strict shifted-Hom bifunctor inverts quasi-isomorphisms"]
theorem shiftedHomSourceBifunctor_map_isIso_of_quasiIso
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ)
    {T T' : (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ} (f : T ⟶ T')
    (hf : DifferentialGradedBimodule.quasiIso A B f.unop) :
    IsIso ((shiftedHomSourceBifunctor A B n).map f) := sorry

/-- The strict-source cohomology bifunctor inverts all bimodule quasi-isomorphisms. -/
@[stacks 0CS5 "cohomology comparison source inverts bimodule quasi-isomorphisms"]
theorem uliftSourceBifunctor_inverts
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.quasiIso A B).op.IsInvertedBy
      (uliftSourceBifunctor A B n) := sorry

/-- The strict-source shifted-Hom bifunctor inverts all bimodule quasi-isomorphisms. -/
@[stacks 0CS5 "shifted-Hom source inverts bimodule quasi-isomorphisms"]
theorem shiftedHomSourceBifunctor_inverts
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.quasiIso A B).op.IsInvertedBy
      (shiftedHomSourceBifunctor A B n) := sorry

/-- Lemma 22.31.4 (0CS5) before localization: the comparison is natural on the opposite
category of strict bimodules and in the derived target. -/
@[stacks 0CS5 "strict-source derived internal-Hom cohomology comparison"]
noncomputable def uliftSourceBifunctorIso
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    uliftSourceBifunctor A B n ≅ shiftedHomSourceBifunctor A B n :=
  NatIso.ofComponents (fun T ↦ uliftIso T.unop n)
    (fun f ↦ uliftIso_naturality_source f.unop n)

/-- The strict-source comparison at a bimodule is the canonical fixed-source comparison. -/
@[simp, stacks 0CS5 "strict-source comparison component"]
theorem uliftSourceBifunctorIso_app
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ)
    (T : (DifferentialGradedBimodule.{u, w, w, x} A B)ᵒᵖ) :
    (uliftSourceBifunctorIso A B n).app T = uliftIso T.unop n := sorry

/-- Lifted derived internal-Hom cohomology as a functor of the opposite derived bimodule
category. -/
@[stacks 0CS5 "cohomology bifunctor on the derived bimodule category"]
noncomputable def uliftBifunctor (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.Derived.Category.{u, w, w, x} A B)ᵒᵖ ⥤
      (DifferentialGradedModule.Derived.Category.{u, w, x} B ⥤
        ModuleCat.{max (max u (w + 1)) x} R) :=
  InternalHom.derivedBifunctor A B ⋙
    (Functor.whiskeringRight _ _ _).obj
      (DifferentialGradedModule.Derived.Homology.uliftFunctor A n ⋙
        ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R)

/-- The derived cohomology bifunctor is additive in its derived-bimodule variable. -/
@[stacks 0CS5 "additivity of the derived internal-Hom cohomology bifunctor"]
noncomputable instance uliftBifunctorAdditive (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (uliftBifunctor A B n).Additive := sorry

/-- The derived cohomology bifunctor is `R`-linear in its derived-bimodule variable. -/
@[stacks 0CS5 "linearity of the derived internal-Hom cohomology bifunctor"]
noncomputable instance uliftBifunctorLinear (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    Functor.Linear R (uliftBifunctor A B n) := sorry

/-- Fixing a derived bimodule in the cohomology bifunctor gives an additive functor of the
derived target. -/
@[stacks 0CS5 "additivity of derived internal-Hom cohomology at a derived bimodule"]
noncomputable instance uliftBifunctorObjAdditive (
    T : (DifferentialGradedBimodule.Derived.Category.{u, w, w, x} A B)ᵒᵖ) (n : ℤ) :
    ((uliftBifunctor A B n).obj T).Additive := sorry

/-- Fixing a derived bimodule in the cohomology bifunctor gives an `R`-linear functor of the
derived target. -/
@[stacks 0CS5 "linearity of derived internal-Hom cohomology at a derived bimodule"]
noncomputable instance uliftBifunctorObjLinear (
    T : (DifferentialGradedBimodule.Derived.Category.{u, w, w, x} A B)ᵒᵖ) (n : ℤ) :
    Functor.Linear R ((uliftBifunctor A B n).obj T) := sorry

/-- Shifted Hom as a functor of the opposite derived bimodule category. -/
@[stacks 0CS5 "shifted-Hom bifunctor on the derived bimodule category"]
noncomputable def shiftedHomBifunctor
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.Derived.Category.{u, w, w, x} A B)ᵒᵖ ⥤
      (DifferentialGradedModule.Derived.Category.{u, w, x} B ⥤
        ModuleCat.{max (max u (w + 1)) x} R) :=
  (DifferentialGradedBimodule.Derived.forgetToRightModule A B).op ⋙
    ShiftedHom.linearCoyoneda R
      (DifferentialGradedModule.Derived.Category B) n

/-- The shifted-Hom bifunctor is additive in its derived-bimodule variable. -/
@[stacks 0CS5 "additivity of the shifted-Hom bifunctor"]
noncomputable instance shiftedHomBifunctorAdditive (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (shiftedHomBifunctor A B n).Additive := sorry

/-- The shifted-Hom bifunctor is `R`-linear in its derived-bimodule variable. -/
@[stacks 0CS5 "linearity of the shifted-Hom bifunctor"]
noncomputable instance shiftedHomBifunctorLinear (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    Functor.Linear R (shiftedHomBifunctor A B n) := sorry

/-- Fixing a derived bimodule in the shifted-Hom bifunctor gives an additive functor of the
derived target. -/
@[stacks 0CS5 "additivity of shifted Hom at a derived bimodule"]
noncomputable instance shiftedHomBifunctorObjAdditive (
    T : (DifferentialGradedBimodule.Derived.Category.{u, w, w, x} A B)ᵒᵖ) (n : ℤ) :
    ((shiftedHomBifunctor A B n).obj T).Additive := sorry

/-- Fixing a derived bimodule in the shifted-Hom bifunctor gives an `R`-linear functor of the
derived target. -/
@[stacks 0CS5 "linearity of shifted Hom at a derived bimodule"]
noncomputable instance shiftedHomBifunctorObjLinear (
    T : (DifferentialGradedBimodule.Derived.Category.{u, w, w, x} A B)ᵒᵖ) (n : ℤ) :
    Functor.Linear R ((shiftedHomBifunctor A B n).obj T) := sorry

/-- The derived cohomology bifunctor factors the strict-source construction through
localization. -/
@[stacks 0CS5 "strict factorization of the derived cohomology bifunctor"]
noncomputable def uliftBifunctorFactors
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.Derived.fromBimodules A B).op ⋙
        uliftBifunctor A B n ≅
      uliftSourceBifunctor A B n :=
  Functor.isoWhiskerRight (InternalHom.derivedBifunctorFactors A B)
    ((Functor.whiskeringRight _ _ _).obj
      (DifferentialGradedModule.Derived.Homology.uliftFunctor A n ⋙
        ModuleCat.uliftFunctor.{max (max u (w + 1)) x, max u (w + 1)} R))

/-- The derived shifted-Hom bifunctor factors the strict-source construction through
localization. -/
@[stacks 0CS5 "strict factorization of the shifted-Hom bifunctor"]
noncomputable def shiftedHomBifunctorFactors
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    (DifferentialGradedBimodule.Derived.fromBimodules A B).op ⋙
        shiftedHomBifunctor A B n ≅
      shiftedHomSourceBifunctor A B n :=
  Functor.isoWhiskerRight
    (NatIso.op
      (DifferentialGradedBimodule.Derived.forgetToRightModuleFactors A B)).symm
    (ShiftedHom.linearCoyoneda R
      (DifferentialGradedModule.Derived.Category B) n)

/-- At the derived image of a strict bimodule, the cohomology bifunctor recovers its
strict-source cohomology functor. -/
@[stacks 0CS5 "derived cohomology bifunctor at a strict bimodule"]
noncomputable def uliftBifunctorObjIso
    (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    (uliftBifunctor A B n).obj
        (op (DifferentialGradedBimodule.Derived.object T)) ≅
      uliftFunctor T n :=
  (uliftBifunctorFactors A B n).app (op T)

/-- At the derived image of a strict bimodule, the shifted-Hom bifunctor recovers shifted Hom
from its underlying right derived object. -/
@[stacks 0CS5 "shifted-Hom bifunctor at a strict bimodule"]
noncomputable def shiftedHomBifunctorObjIso
    (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    (shiftedHomBifunctor A B n).obj
        (op (DifferentialGradedBimodule.Derived.object T)) ≅
      shiftedHomFunctor T n :=
  (shiftedHomBifunctorFactors A B n).app (op T)

/-- The cohomology bifunctor is the chosen localization lift of its strict-source model. -/
@[stacks 0CS5 "localization lift of the cohomology bifunctor"]
noncomputable instance uliftBifunctorLifting (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    Localization.Lifting
      (DifferentialGradedBimodule.Derived.fromBimodules A B).op
      (DifferentialGradedBimodule.quasiIso A B).op
      (uliftSourceBifunctor A B n) (uliftBifunctor A B n) :=
  ⟨uliftBifunctorFactors A B n⟩

/-- The shifted-Hom bifunctor is the chosen localization lift of its strict-source model. -/
@[stacks 0CS5 "localization lift of the shifted-Hom bifunctor"]
noncomputable instance shiftedHomBifunctorLifting (A : CochainDGAlgebra.{u, w} R)
    (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    Localization.Lifting
      (DifferentialGradedBimodule.Derived.fromBimodules A B).op
      (DifferentialGradedBimodule.quasiIso A B).op
      (shiftedHomSourceBifunctor A B n) (shiftedHomBifunctor A B n) :=
  ⟨shiftedHomBifunctorFactors A B n⟩

/-- Lemma 22.31.4 (0CS5), fully derived and bifunctorial: the cohomology/Ext comparison is
contravariantly natural in the derived bimodule and covariantly natural in the derived target. -/
@[stacks 0CS5 "bifunctorial derived internal-Hom cohomology comparison"]
noncomputable def uliftBifunctorIso
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    uliftBifunctor A B n ≅ shiftedHomBifunctor A B n :=
  Localization.liftNatIso
    (DifferentialGradedBimodule.Derived.fromBimodules A B).op
    (DifferentialGradedBimodule.quasiIso A B).op
    (uliftSourceBifunctor A B n) (shiftedHomSourceBifunctor A B n)
    (uliftBifunctor A B n) (shiftedHomBifunctor A B n)
    (uliftSourceBifunctorIso A B n)

/-- On a strict representative, the fully derived comparison is the fixed-source comparison
conjugated by the two canonical factorization isomorphisms. -/
@[stacks 0CS5 "component of the derived cohomology comparison at a strict bimodule"]
theorem uliftBifunctorIso_hom_app
    (T : DifferentialGradedBimodule.{u, w, w, x} A B) (n : ℤ) :
    (uliftBifunctorIso A B n).hom.app
        (op (DifferentialGradedBimodule.Derived.object T)) =
      (uliftBifunctorObjIso T n).hom ≫ (uliftIso T n).hom ≫
        (shiftedHomBifunctorObjIso T n).inv := sorry

/-- Pulling the derived comparison back to strict bimodules recovers the strict-source
comparison, up to the canonical localization factorization isomorphisms. -/
@[stacks 0CS5 "pullback of the derived cohomology comparison to strict bimodules"]
theorem uliftBifunctorIso_fromBimodules
    (A : CochainDGAlgebra.{u, w} R) (B : CochainDGAlgebra.{u, x} R) (n : ℤ) :
    Functor.isoWhiskerLeft
        (DifferentialGradedBimodule.Derived.fromBimodules A B).op
        (uliftBifunctorIso A B n) =
      uliftBifunctorFactors A B n ≪≫ uliftSourceBifunctorIso A B n ≪≫
        (shiftedHomBifunctorFactors A B n).symm := sorry

variable (T : DifferentialGradedBimodule.{u, w, w, x} A B)
variable (K : (DifferentialGradedBimodule.Derived.Category.{u, w, w, x} A B)ᵒᵖ)

#synth (uliftFunctor T 0).Additive
#synth Functor.Linear R (uliftFunctor T 0)
#synth (shiftedHomFunctor T 0).Additive
#synth Functor.Linear R (shiftedHomFunctor T 0)
#synth (uliftSourceBifunctor A B 0).Additive
#synth Functor.Linear R (uliftSourceBifunctor A B 0)
#synth (shiftedHomSourceBifunctor A B 0).Additive
#synth Functor.Linear R (shiftedHomSourceBifunctor A B 0)
#synth (uliftBifunctor A B 0).Additive
#synth Functor.Linear R (uliftBifunctor A B 0)
#synth ((uliftBifunctor A B 0).obj K).Additive
#synth Functor.Linear R ((uliftBifunctor A B 0).obj K)
#synth (shiftedHomBifunctor A B 0).Additive
#synth Functor.Linear R (shiftedHomBifunctor A B 0)
#synth ((shiftedHomBifunctor A B 0).obj K).Additive
#synth Functor.Linear R ((shiftedHomBifunctor A B 0).obj K)

end DifferentialGradedBimodule.InternalHom.Derived.Cohomology
