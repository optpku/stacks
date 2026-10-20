module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.CanonicalElement
public import ReasLib.AlgebraicGeometry.GroupoidsOver.InfinitesimalDeformation.Functoriality
public import ReasLib.AlgebraicGeometry.Scheme.Morphism.FiniteType.Point
public import ReasLib.CategoryTheory.Fibered.YonedaEvaluation.Groupoids
public import ReasLib.CategoryTheory.Fibered.CartesianBasedFunctor.YonedaEvaluation.Slice.Chosen
public import ReasLib.CategoryTheory.Functor.IsomorphismClasses
public import Mathlib.RingTheory.FiniteType

/-!
# Canonical elements and residue tangent spaces

The differential section parametrizes affine residue tangent vectors. Restriction
of the canonical element agrees with the tangent map induced by a fibre object.
-/

@[expose] public section

-- The restriction map uses a private comparison of residue fibre objects.
set_option backward.privateInPublic true

open CategoryTheory AlgebraicGeometry Functor
open FiberedCategoryOver.Groupoids
open TrivSqZeroExt

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The coefficient ring as a module over the source ring by restriction of scalars. -/
def residueModule {A : CommRingCat.{u}} {k : Type u} [CommRing k]
    (π : A ⟶ CommRingCat.of k) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars π.hom).obj (ModuleCat.of k k)

/-- The residue coefficient module is restriction of scalars of the regular module. -/
theorem residueModule_eq {A : CommRingCat.{u}} {k : Type u} [CommRing k]
    (π : A ⟶ CommRingCat.of k) :
    residueModule π = (ModuleCat.restrictScalars π.hom).obj (ModuleCat.of k k) := rfl

variable {S : Scheme.{u}} {Λ A : CommRingCat.{u}} (v : Λ ⟶ A)
variable {σΛ : Spec Λ ⟶ S} {σA : Spec A ⟶ S} (hv : Spec.map v ≫ σΛ = σA)
variable (u0 : Spec A) (π : A ⟶ (Spec A).residueField u0)

/-- The differential section with residue coefficients sends `a` to `(π(a), θ(d a))`. -/
def residueDifferentialSection
    (θ : CommRingCat.KaehlerDifferential v ⟶ residueModule π) :
    A ⟶ trivSqZero ((Spec A).residueField u0)
      (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)) :=
  trivSqZeroCan v ≫ trivSqZeroMapRestrict π θ

/-- The two coordinates of the residue differential section are the residue map and
its prescribed differential. -/
theorem residueDifferentialSection_apply
    (θ : CommRingCat.KaehlerDifferential v ⟶ residueModule π) (a : A) :
    (residueDifferentialSection v u0 π θ).hom a =
      (π.hom a, θ (CommRingCat.KaehlerDifferential.d a)) := by
  change (π.hom (a + 0), θ (0 + CommRingCat.KaehlerDifferential.d a)) = _
  simp only [add_zero, zero_add]

/-- The residue differential section lifts the residue ring map. -/
theorem residueDifferentialSection_comp_fst
    (θ : CommRingCat.KaehlerDifferential v ⟶ residueModule π) :
    residueDifferentialSection v u0 π θ ≫
      trivSqZeroHom ((Spec A).residueField u0)
        (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)) = π := sorry

include hv in
/-- The spectrum of the residue differential section is a morphism over the base scheme. -/
theorem residueDifferentialSection_spec
    (θ : CommRingCat.KaehlerDifferential v ⟶ residueModule π) :
    Spec.map (residueDifferentialSection v u0 π θ) ≫ σA =
      specTrivSqZero (Spec.map π ≫ σA)
        (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)) := sorry

/-- The residue point as a fibre object of the affine scheme's canonical slice fibration. -/
def affineResiduePoint :
    (GroupoidsOver.slice (Over.mk σA)).p.Fiber (Over.mk (Spec.map π ≫ σA)) :=
  ⟨Over.mk (specOverHom π rfl), rfl⟩

variable {X : GroupoidsOver S} (x : X.p.Fiber (Over.mk σA))

/-- The restriction of a fibre object to a residue point via its Yoneda representative. -/
def residueObject : X.p.Fiber (Over.mk (Spec.map π ≫ σA)) :=
  (fiberFunctor (YonedaSlice.representative x) _).obj (affineResiduePoint u0 π)

/-- The Yoneda section at the residue point is the selected pullback of the fibre object. -/
private def residueComparison :
    Chosen.reindexObj X.p (specOverHom π rfl) x ≅ residueObject u0 π x :=
  (CartesianBasedFunctor.Yoneda.Slice.Chosen.sectionIso X.p x
    (Over.mk (specOverHom π rfl))).symm

/-- An affine tangent vector is the class of the dual-number lift of its differential section. -/
def affineTangentVector (θ : CommRingCat.KaehlerDifferential v ⟶ residueModule π) :
    (tangentFunctor (affineResiduePoint (σA := σA) u0 π)).obj
      (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)) :=
  (tangentForget (affineResiduePoint (σA := σA) u0 π) _).symm
    (lifts.mk (UnderLift.ofHom
      (specOverHom (trivSqZeroHom ((Spec A).residueField u0)
        (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)))
        (trivSqZeroHom_comp (Spec.map π ≫ σA) _))
      (affineResiduePoint u0 π)
      (Over.homMk
        (specOverHom (trivSqZeroHom ((Spec A).residueField u0)
          (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)))
          (trivSqZeroHom_comp (Spec.map π ≫ σA) _))
        (V := Over.mk (specOverHom (residueDifferentialSection v u0 π θ)
          (residueDifferentialSection_spec v hv u0 π θ)))
        (by
          apply Over.OverMorphism.ext
          change Spec.map _ ≫ Spec.map _ = Spec.map π
          rw [← Spec.map_comp, residueDifferentialSection_comp_fst]))
      (h := by
        apply IsHomLift.of_fac _ _ _ rfl rfl
        simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
        rfl)))

/-- Linear maps from Kähler differentials parametrize all affine residue tangent vectors. -/
theorem affineTangentVector_bijective (h_open : IsOpenImmersion σΛ)
    (hπ : Spec.map π = (Spec A).fromSpecResidueField u0) :
    Function.Bijective (affineTangentVector v hv (σA := σA) u0 π) := sorry

/-- The trivial extension by the residue field is the pullback of the residue dual numbers. -/
theorem residueSquare_isPullback :
    CategoryTheory.IsPullback
      (trivSqZeroHom A (residueModule π))
      (trivSqZeroMapRestrict π (𝟙 (residueModule π)))
      π (trivSqZeroHom ((Spec A).residueField u0)
        (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0))) := sorry

variable [HasStrongRimSchlessinger X]

/-- Restriction from the original object to its residue object on tangent spaces. -/
def residueTangentMap :
    (tangentFunctor x).obj (residueModule π) →
      (tangentFunctor (residueObject u0 π x)).obj
        (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)) :=
  tangentMap π rfl (𝟙 (residueModule π)) x (residueObject u0 π x)
    (residueComparison u0 π x).hom

/-- Under the strong Rim-Schlessinger condition, restriction identifies the two residue
tangent spaces. -/
theorem residueTangentMap_bijective :
    Function.Bijective (residueTangentMap u0 π x) := sorry

/-- The tangent map of the object-induced Yoneda morphism on the entire affine residue
tangent space. -/
def inducedTangentMap :
    (tangentFunctor (affineResiduePoint (σA := σA) u0 π)).obj
        (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)) →
      (tangentFunctor (residueObject u0 π x)).obj
        (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)) :=
  fun t ↦ (tangentForget (residueObject u0 π x) _).symm
    (CategoryTheory.Functor.isoClassesMap
      (FiberedCategoryOver.Groupoids.liftFunctor.onId (YonedaSlice.representative x)
        (specOverHom (trivSqZeroHom ((Spec A).residueField u0)
          (ModuleCat.of ((Spec A).residueField u0) ((Spec A).residueField u0)))
          (trivSqZeroHom_comp (Spec.map π ≫ σA) _))
        (affineResiduePoint u0 π))
      (tangentForget (affineResiduePoint (σA := σA) u0 π) _ t))

/-- The object-induced tangent map evaluates a residue derivation on the canonical element,
then restricts the resulting deformation to the residue object. -/
theorem inducedTangentMap_apply (h_open : IsOpenImmersion σΛ)
    (h_noetherian : IsNoetherianRing Λ) (h_finiteType : v.hom.FiniteType)
    (h_finiteTypePoint : IsFiniteTypePoint u0)
    (hπ : Spec.map π = (Spec A).fromSpecResidueField u0)
    (θ : CommRingCat.KaehlerDifferential v ⟶ residueModule π) :
    inducedTangentMap u0 π x (affineTangentVector v hv u0 π θ) =
      residueTangentMap u0 π x
        ((tangentFunctor x).map θ (canonicalElement v hv x h_open)) := sorry

end AlgebraicGeometry.GroupoidsOver
