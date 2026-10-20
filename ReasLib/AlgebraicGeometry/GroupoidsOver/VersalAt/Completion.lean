module

public import ReasLib.AlgebraicGeometry.GroupoidsOver.Completion
public import ReasLib.AlgebraicGeometry.GroupoidsOver.FormalObject.ResiduePredeformation
public import ReasLib.AlgebraicGeometry.GroupoidsOver.VersalAt
public import ReasLib.AlgebraicGeometry.FormalDeformation.FormalObject.Versal

/-! # Versality and completed-stalk formal objects -/

@[expose] public section

open CategoryTheory AlgebraicGeometry Functor IsLocalRing
open scoped AlgebraicGeometry

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidsOver

/-- The residue-point predeformation projection of the completed-stalk formal
object is cofibered in groupoids. -/
instance instIsFiberedInGroupoidsOp_toPredeformation
    {S : Scheme.{u}} [IsLocallyNoetherian S] {X : GroupoidsOver S}
    {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU] (x : X.total)
    (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0]
    {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
    [Algebra Λ (associatedFormalObject hU x hx u0).base.carrier]
    [Module.Finite Λ
      (ResidueField (associatedFormalObject hU x hx u0).base.carrier)]
    (openImmersion : Spec (CommRingCat.of Λ) ⟶ S) [IsOpenImmersion openImmersion]
    (h_toS :
      Spec.map (CommRingCat.ofHom
            (algebraMap Λ (associatedFormalObject hU x hx u0).base.carrier)) ≫
          openImmersion =
        (associatedFormalObject hU x hx u0).base.toS) :
    Functor.IsFibered.InGroupoids
      (FormalObject.predeformationProjection
        (associatedFormalObject hU x hx u0) openImmersion h_toS).op :=
  sorry

/-- An object over a scheme locally of finite type over a locally Noetherian
base is versal at a finite type point if and only if its completed-stalk formal
object is versal over every compatible affine-open coefficient presentation. -/
theorem isVersalAt_iff_isVersal {S : Scheme.{u}} [IsLocallyNoetherian S]
    {X : GroupoidsOver S} {U : Scheme.{u}} (hU : U ⟶ S) [LocallyOfFiniteType hU]
    (x : X.total) (hx : X.p.obj x = Over.mk hU) (u0 : U) [IsFiniteTypePoint u0] :
    IsVersalAt hU x hx u0 ↔
      ∀ {Λ : Type u} [CommRing Λ] [IsNoetherianRing Λ]
        [Algebra Λ (associatedFormalObject hU x hx u0).base.carrier]
        [Module.Finite Λ
          (ResidueField (associatedFormalObject hU x hx u0).base.carrier)]
        (openImmersion : Spec (CommRingCat.of Λ) ⟶ S)
        [IsOpenImmersion openImmersion]
        (h_toS :
          Spec.map (CommRingCat.ofHom
                (algebraMap Λ
                  (associatedFormalObject hU x hx u0).base.carrier)) ≫
              openImmersion =
            (associatedFormalObject hU x hx u0).base.toS),
        _root_.FormalObject.IsVersal
          (FormalObject.toPredeformation
            (associatedFormalObject hU x hx u0) openImmersion h_toS) :=
  sorry

end AlgebraicGeometry.GroupoidsOver
