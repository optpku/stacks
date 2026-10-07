module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Defs
public import stacks_project.Chap59.Lemma_59_51_9_PushforwardSystem

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Etale.SheafSystem

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.Etale

variable {X Y X' Y' : Scheme.{u}}
variable (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
variable (h_cart : IsPullback g' f' f g)
variable (F : Sheaf X.smallEtaleTopology (Type (u + 1)))

/-- The adjunction-mate comparison `g^{-1} f_* F ⟶ f'_* (g')^{-1} F` for a
cartesian square of schemes. -/
noncomputable def finiteBaseChangeHom :
    pullbackAlong g (pushforwardAlong f F) ⟶
      pushforwardAlong f' (pullbackAlong g' F) :=
  (((smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
        Y.smallEtaleTopology Y'.smallEtaleTopology).homEquiv
      (pushforwardAlong f F) (pushforwardAlong f' (pullbackAlong g' F))).symm
    (((smallEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
          Y.smallEtaleTopology X.smallEtaleTopology).map
        (((smallEtalePullback g').sheafAdjunctionContinuous (Type (u + 1))
            X.smallEtaleTopology X'.smallEtaleTopology).unit.app F) ≫
      (pushforwardCompIso g' f).hom.app (pullbackAlong g' F) ≫
      eqToHom (congrArg (fun t ↦ pushforwardAlong t (pullbackAlong g' F)) h_cart.w) ≫
      (pushforwardCompIso f' g).inv.app (pullbackAlong g' F))

/-- The comparison is the adjunction mate of the unit of `g'` transported along
the cartesian identification `g' ≫ f = f' ≫ g`. -/
theorem finiteBaseChangeHom_eq :
    finiteBaseChangeHom f g f' g' h_cart F =
      (((smallEtalePullback g).sheafAdjunctionContinuous (Type (u + 1))
            Y.smallEtaleTopology Y'.smallEtaleTopology).homEquiv
          (pushforwardAlong f F)
          (pushforwardAlong f' (pullbackAlong g' F))).symm
        (((smallEtalePullback f).sheafPushforwardContinuous (Type (u + 1))
              Y.smallEtaleTopology X.smallEtaleTopology).map
            (((smallEtalePullback g').sheafAdjunctionContinuous (Type (u + 1))
                X.smallEtaleTopology X'.smallEtaleTopology).unit.app F) ≫
          (pushforwardCompIso g' f).hom.app (pullbackAlong g' F) ≫
          eqToHom (congrArg (fun t ↦ pushforwardAlong t (pullbackAlong g' F))
            h_cart.w) ≫
          (pushforwardCompIso f' g).inv.app (pullbackAlong g' F)) :=
  sorry

/-- Lemma 59.55.3: if `f` is finite and the square is cartesian, then for any
sheaf of sets `F` on `X` étale the comparison
`g^{-1} f_* F ⟶ f'_* (g')^{-1} F` is an isomorphism. -/
@[stacks 0959]
theorem finite_baseChange_isIso [IsFinite f] :
    IsIso (finiteBaseChangeHom f g f' g' h_cart F) := sorry

end AlgebraicGeometry.Scheme.Etale

end

end
