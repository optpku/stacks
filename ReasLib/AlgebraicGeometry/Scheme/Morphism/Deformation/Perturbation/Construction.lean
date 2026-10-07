module

public import ReasLib.AlgebraicGeometry.Scheme.Morphism.Deformation.Perturbation

/-!
# Explicit construction of perturbations

Differential parameters determine morphisms between the square-zero presentations of
first-order thickenings and hence perturbations of the original scheme morphisms.
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace
open SheafOfModules.RingedSite
open scoped AlgebraicGeometry RelativeDerivation

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Hom.Deformation

variable {S X X' Y Y' : Scheme.{u}}

/-- The conormal contribution of a differential parameter, read in the target presentation
ring over `U`. -/
noncomputable def presentationConormalTerm (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y)
    [X.Over S] [Y.Over S] [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [a.IsOver S]
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i)
    (U : (Opens Y)ᵒᵖ)
    (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U) :
    ((TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
      (IsFirstOrderThickening.presentationSheaf i)).obj.obj U :=
  (SquareZeroExtension.conormalInclusion
    (IsFirstOrderThickening.presentationProjection i)
    (IsFirstOrderThickening.presentationKernel_isSquareZero i)).hom.app
      ((Opens.map a.base).op.obj U)
      ((d[(Y ↘ S).toShHom].postcomp
        (((Scheme.Modules.pullbackPushforwardAdjunction a).homEquiv _ _) θ).val).d
          ((IsFirstOrderThickening.presentationProjection j).hom.app U x))

/-- The sectionwise formula that perturbs the presentation map of a deformation by a map from
relative differentials to the conormal sheaf. -/
noncomputable def presentationPerturbApply (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i)
    (U : (Opens Y)ᵒᵖ)
    (x : (IsFirstOrderThickening.presentationSheaf j).obj.obj U) :
    ((TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
      (IsFirstOrderThickening.presentationSheaf i)).obj.obj U :=
  (Scheme.Hom.Conormal.presentationMap sq).hom.app U x -
    presentationConormalTerm S i j a θ U x

/-- The presentation perturbation formula preserves zero. -/
theorem presentationPerturbApply_zero (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) (U : (Opens Y)ᵒᵖ) :
    presentationPerturbApply S i j a a' sq θ U 0 = 0 := sorry

/-- The presentation perturbation formula preserves one. -/
theorem presentationPerturbApply_one (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) (U : (Opens Y)ᵒᵖ) :
    presentationPerturbApply S i j a a' sq θ U 1 = 1 := sorry

/-- The presentation perturbation formula preserves addition. -/
theorem presentationPerturbApply_add (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) (U : (Opens Y)ᵒᵖ)
    (x y : (IsFirstOrderThickening.presentationSheaf j).obj.obj U) :
    presentationPerturbApply S i j a a' sq θ U (x + y) =
      presentationPerturbApply S i j a a' sq θ U x +
        presentationPerturbApply S i j a a' sq θ U y := sorry

/-- The presentation perturbation formula preserves multiplication. -/
theorem presentationPerturbApply_mul (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) (U : (Opens Y)ᵒᵖ)
    (x y : (IsFirstOrderThickening.presentationSheaf j).obj.obj U) :
    presentationPerturbApply S i j a a' sq θ U (x * y) =
      presentationPerturbApply S i j a a' sq θ U x *
        presentationPerturbApply S i j a a' sq θ U y := sorry

/-- The ring homomorphism on sections supplied by the presentation perturbation formula. -/
noncomputable def presentationPerturbRingHom (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) (U : (Opens Y)ᵒᵖ) :
    (IsFirstOrderThickening.presentationSheaf j).obj.obj U →+*
      ((TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
        (IsFirstOrderThickening.presentationSheaf i)).obj.obj U where
  toFun := presentationPerturbApply S i j a a' sq θ U
  map_zero' := presentationPerturbApply_zero S i j a a' sq θ U
  map_one' := presentationPerturbApply_one S i j a a' sq θ U
  map_add' := presentationPerturbApply_add S i j a a' sq θ U
  map_mul' := presentationPerturbApply_mul S i j a a' sq θ U

/-- The presentation perturbation formula commutes with restriction maps. -/
theorem presentationPerturbRingHom_naturality (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) {U V : (Opens Y)ᵒᵖ} (f : U ⟶ V) :
    (IsFirstOrderThickening.presentationSheaf j).obj.map f ≫
        CommRingCat.ofHom (presentationPerturbRingHom S i j a a' sq θ V) =
      CommRingCat.ofHom (presentationPerturbRingHom S i j a a' sq θ U) ≫
        ((TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
          (IsFirstOrderThickening.presentationSheaf i)).obj.map f := sorry

/-- The explicit perturbed map between the square-zero presentation sheaves. -/
noncomputable def presentationPerturbation (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) :
    IsFirstOrderThickening.presentationSheaf j ⟶
      (TopCat.Sheaf.pushforward CommRingCat.{u} a.base).obj
        (IsFirstOrderThickening.presentationSheaf i) :=
  ObjectProperty.homMk
    { app U := CommRingCat.ofHom (presentationPerturbRingHom S i j a a' sq θ U)
      naturality := fun _ _ f ↦
        presentationPerturbRingHom_naturality S i j a a' sq θ f }

/-- The presheafed-space map between the reconstructed square-zero extensions determined by
the perturbed presentation map. -/
noncomputable def presentationPerturbToHom (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) :
    (IsFirstOrderThickening.reconstructedScheme i).toPresheafedSpace ⟶
      (IsFirstOrderThickening.reconstructedScheme j).toPresheafedSpace where
  base := a.base
  c := (presentationPerturbation S i j a a' sq θ).hom

/-- The perturbed presentation induces local homomorphisms on all stalks. -/
theorem presentationPerturbToHom_isLocalHom (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i)
    (x : IsFirstOrderThickening.reconstructedScheme i) :
    IsLocalHom ((presentationPerturbToHom S i j a a' sq θ).stalkMap x).hom := sorry

/-- The scheme morphism between the reconstructed thickenings induced by explicit
presentation perturbation. -/
noncomputable def presentationPerturbHom (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) :
    IsFirstOrderThickening.reconstructedScheme i ⟶
      IsFirstOrderThickening.reconstructedScheme j :=
  ⟨⟨presentationPerturbToHom S i j a a' sq θ,
    presentationPerturbToHom_isLocalHom S i j a a' sq θ⟩⟩

/-- Perturb a morphism between first-order thickenings by a map from relative differentials,
using the explicit square-zero presentation formula. -/
noncomputable def perturbHom (S : Scheme.{u}) (i : X ⟶ X') (j : Y ⟶ Y')
    (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) : X' ⟶ Y' :=
  (inv (IsFirstOrderThickening.reconstructionOverHom i S)).left ≫
    presentationPerturbHom S i j a a' sq θ ≫
      IsFirstOrderThickening.reconstructionHom j

/-- The explicit perturbed morphism realizes the prescribed deformation parameter. -/
theorem perturbHom_isPerturbation (S : Scheme.{u}) (i : X ⟶ X')
    (j : Y ⟶ Y') (a : X ⟶ Y) (a' : X' ⟶ Y')
    [X.Over S] [X'.Over S] [Y.Over S] [Y'.Over S]
    [IsFirstOrderThickening i] [IsFirstOrderThickening j]
    [i.IsOver S] [j.IsOver S] [a.IsOver S] [a'.IsOver S]
    (sq : CommSq a i j a')
    (θ : (Scheme.Modules.pullback a).obj Ω[(Y ↘ S).toShHom] ⟶
      Scheme.Hom.conormalSheaf i) :
    IsPerturbation S i j a a' sq θ (perturbHom S i j a a' sq θ) := sorry

end AlgebraicGeometry.Scheme.Hom.Deformation
