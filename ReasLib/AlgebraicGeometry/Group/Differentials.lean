module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.Free.Pullback
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.BaseChange
public import ReasLib.AlgebraicGeometry.Scheme.Differentials.Conormal.Splitting
public import ReasLib.AlgebraicGeometry.Scheme.Module.Conormal.Quasicoherent
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.LinearAlgebra.Basis.VectorSpace

@[expose] public section

open CategoryTheory Limits
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open CategoryTheory.MonObj
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.GroupDifferentials

/-- The section of `G ⊗ G` over `G` given on points by `g ↦ (g, e)`. -/
def rightUnitSection {S : Scheme.{u}} (G : Over S) [GrpObj G] : G ⟶ G ⊗ G :=
  lift (𝟙 G) (toUnit G ≫ η[G])

/-- The first projection of `rightUnitSection G` is the identity. -/
theorem rightUnitSection_fst {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (rightUnitSection G).left ≫ (fst G G).left = 𝟙 G.left := sorry

/-- The second projection of `rightUnitSection G` is the identity section after the structure
morphism. -/
theorem rightUnitSection_snd {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (rightUnitSection G).left ≫ (snd G G).left = G.hom ≫ η[G].left := sorry

/-- Multiplication after `rightUnitSection G` is the identity of `G`. -/
theorem rightUnitSection_mul {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (rightUnitSection G).left ≫ μ[G].left = 𝟙 G.left := sorry

/-- The square formed by multiplication, the first projection, and the two structure maps of a
group scheme is cartesian. -/
theorem mulSquareIsPullback {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsPullback μ[G].left (fst G G).left G.hom G.hom := sorry

/-- The defining pullback square of `G ⊗ G`, with the second projection horizontal. -/
theorem projectionSquareIsPullback {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsPullback (snd G G).left (fst G G).left G.hom G.hom := sorry

/-- The relative-differentials comparison associated to the cartesian multiplication square. -/
def mulComparison {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (RingedSpace.Hom.pullback μ[G].left.toShHom).obj Ω[G.hom.toShHom] ⟶
      Ω[(fst G G).left.toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    ((mulSquareIsPullback G).toCommSq.map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The multiplication comparison is the canonical differential comparison of its cartesian
square. -/
theorem mulComparison_spec {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    mulComparison G =
      RingedSpace.Hom.Differentials.comparison
        ((mulSquareIsPullback G).toCommSq.map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace)) := sorry

/-- The relative-differentials comparison for multiplication is an isomorphism. -/
instance mulComparison_isIso {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsIso (mulComparison G) := sorry

/-- The relative-differentials comparison associated to the defining projection square of
`G ⊗ G`. -/
def projectionComparison {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (RingedSpace.Hom.pullback (snd G G).left.toShHom).obj Ω[G.hom.toShHom] ⟶
      Ω[(fst G G).left.toShHom] :=
  RingedSpace.Hom.Differentials.comparison
    ((projectionSquareIsPullback G).toCommSq.map
      (Scheme.forgetToLocallyRingedSpace ⋙
        LocallyRingedSpace.forgetToSheafedSpace))

/-- The projection comparison is the canonical differential comparison of the defining
pullback square. -/
theorem projectionComparison_spec {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    projectionComparison G =
      RingedSpace.Hom.Differentials.comparison
        ((projectionSquareIsPullback G).toCommSq.map
          (Scheme.forgetToLocallyRingedSpace ⋙
            LocallyRingedSpace.forgetToSheafedSpace)) := sorry

/-- The differential comparison for the defining projection square is an isomorphism. -/
instance projectionComparison_isIso {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsIso (projectionComparison G) := sorry

/-- The canonical translation comparison from the relative differentials of a group scheme to
the pullback, along `g ↦ (g, e)`, of the differentials relative to the first projection. -/
def translationComparison {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    Ω[G.hom.toShHom] ⟶
      (Modules.pullback (rightUnitSection G).left).obj Ω[(fst G G).left.toShHom] :=
  (Modules.pullbackId G.left).inv.app Ω[G.hom.toShHom] ≫
    (Modules.pullbackCongr (rightUnitSection_mul G)).inv.app Ω[G.hom.toShHom] ≫
    (Modules.pullbackComp (rightUnitSection G).left μ[G].left).inv.app Ω[G.hom.toShHom] ≫
    (Modules.pullback (rightUnitSection G).left).map (mulComparison G)

/-- The translation comparison is the multiplication differential comparison pulled back along
`g ↦ (g, e)`, with the canonical pullback coherence maps. -/
theorem translationComparison_spec {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    translationComparison G =
      (Modules.pullbackId G.left).inv.app Ω[G.hom.toShHom] ≫
        (Modules.pullbackCongr (rightUnitSection_mul G)).inv.app Ω[G.hom.toShHom] ≫
        (Modules.pullbackComp (rightUnitSection G).left μ[G].left).inv.app
          Ω[G.hom.toShHom] ≫
        (Modules.pullback (rightUnitSection G).left).map (mulComparison G) := sorry

/-- The canonical translation comparison is an isomorphism. -/
instance translationComparison_isIso {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsIso (translationComparison G) := sorry

/-- The identity section of a group scheme is an immersion. -/
instance identitySection_isImmersion {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsImmersion η[G].left := sorry

/-- Pulling back the conormal-to-differentials morphism of the identity section along the
structure map of a group scheme. -/
def conormalComparison {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (Modules.pullback G.hom).obj (Hom.conormalSheaf η[G].left) ⟶
      (Modules.pullback G.hom).obj
        ((Modules.pullback η[G].left).obj Ω[G.hom.toShHom]) :=
  (Modules.pullback G.hom).map
    (Hom.Conormal.Differentials.map η[G].left G.hom)

/-- The conormal comparison is exactly the pullback of the canonical conormal-differentials map
of the identity section. -/
theorem conormalComparison_def {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    conormalComparison G =
      (Modules.pullback G.hom).map
        (Hom.Conormal.Differentials.map η[G].left G.hom) := sorry

/-- The pulled-back conormal comparison at the identity section is an isomorphism. -/
instance conormalComparison_isIso {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsIso (conormalComparison G) := sorry

/-- Over the spectrum of a field, the relative differential sheaf of a group scheme is free. -/
instance differentials_isFree_of_field {k : Type u} [Field k]
    (G : Over (Spec (CommRingCat.of k))) [GrpObj G] :
    SheafOfModules.IsFree Ω[G.hom.toShHom] := sorry

/-- The pullback of the identity-restricted differentials maps canonically to the pullback,
along `g ↦ (g, e)`, of the differentials relative to the first projection. -/
def identityRestrictionComparison {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (Modules.pullback G.hom).obj
        ((Modules.pullback η[G].left).obj Ω[G.hom.toShHom]) ⟶
      (Modules.pullback (rightUnitSection G).left).obj Ω[(fst G G).left.toShHom] :=
  (Modules.pullbackComp G.hom η[G].left).hom.app Ω[G.hom.toShHom] ≫
    (Modules.pullbackCongr (rightUnitSection_snd G)).inv.app Ω[G.hom.toShHom] ≫
    (Modules.pullbackComp (rightUnitSection G).left (snd G G).left).inv.app
      Ω[G.hom.toShHom] ≫
    (Modules.pullback (rightUnitSection G).left).map (projectionComparison G)

/-- The identity-restriction comparison is the projection differential comparison transported
through the canonical pullback coherence maps. -/
theorem identityRestrictionComparison_spec {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    identityRestrictionComparison G =
      (Modules.pullbackComp G.hom η[G].left).hom.app Ω[G.hom.toShHom] ≫
        (Modules.pullbackCongr (rightUnitSection_snd G)).inv.app Ω[G.hom.toShHom] ≫
        (Modules.pullbackComp (rightUnitSection G).left (snd G G).left).inv.app
          Ω[G.hom.toShHom] ≫
        (Modules.pullback (rightUnitSection G).left).map (projectionComparison G) := rfl

/-- The identity-restriction comparison is an isomorphism. -/
instance identityRestrictionComparison_isIso {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsIso (identityRestrictionComparison G) := by
  -- Record the imported projection comparison isomorphism explicitly so the final `mapIso`
  -- factor does not rely on a failing class-search step at `asIso`.
  have hprojection : IsIso (projectionComparison G) := projectionComparison_isIso G
  -- Route correction: keep the goal in the explicit composite-iso normal form, since `simpa`
  -- normalizes the witness term too aggressively for this `IsIso` target.
  change IsIso
    (((Modules.pullbackComp G.hom η[G].left).app Ω[G.hom.toShHom] ≪≫
        ((Modules.pullbackCongr (rightUnitSection_snd G)).app Ω[G.hom.toShHom]).symm ≪≫
        ((Modules.pullbackComp (rightUnitSection G).left (snd G G).left).app
          Ω[G.hom.toShHom]).symm ≪≫
        (Modules.pullback (rightUnitSection G).left).mapIso
          (@asIso _ _ _ _ (projectionComparison G) hprojection)).hom)
  infer_instance

/-- The pulled-back identity conormal sheaf maps canonically to the common product-relative
differential object used by translation invariance. -/
def conormalTranslationComparison {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    (Modules.pullback G.hom).obj (Hom.conormalSheaf η[G].left) ⟶
      (Modules.pullback (rightUnitSection G).left).obj Ω[(fst G G).left.toShHom] :=
  conormalComparison G ≫ identityRestrictionComparison G

/-- The conormal-to-product comparison factors through the identity-restricted relative
differentials. -/
theorem conormalTranslationComparison_spec {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    conormalTranslationComparison G =
      conormalComparison G ≫ identityRestrictionComparison G := rfl

/-- The conormal-to-product comparison is an isomorphism. -/
instance conormalTranslationComparison_isIso {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsIso (conormalTranslationComparison G) := by
  -- Unfold the definition so the goal becomes the composite of the imported conormal
  -- comparison isomorphism with the identity-restriction isomorphism proved above.
  simpa [conormalTranslationComparison] using
    (inferInstance : IsIso (conormalComparison G ≫ identityRestrictionComparison G))

/-- The canonical translation and conormal comparison morphisms of a group scheme are
isomorphisms. -/
theorem invariantDifferentialsComparison_isIso {S : Scheme.{u}} (G : Over S) [GrpObj G] :
    IsIso (translationComparison G) ∧ IsIso (conormalTranslationComparison G) :=
  ⟨inferInstance, inferInstance⟩

end AlgebraicGeometry.Scheme.GroupDifferentials
