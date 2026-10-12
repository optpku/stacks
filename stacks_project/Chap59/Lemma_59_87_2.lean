/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.GeometricallyReduced
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme

/-Lemma 59.87.2: for a cartesian square of schemes with `f` flat and locally of finite
presentation with geometrically reduced fibres, and for every sheaf of sets `F` on `T_étale`,
the comparison `f⁻¹ g_* F ⟶ h_* e⁻¹ F` is an isomorphism. -/
@[stacks 0EYS] #check (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_geometricallyReduced :
  ∀ {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    (cart : IsPullback h e f g) (F : Sheaf T.smallEtaleTopology (Type (u + 1))),
    IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g cart F))

/- Each component of the étale sheaf base-change comparison is an isomorphism. -/
#check (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_geometricallyReduced_app :
  ∀ {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] [GeometricallyReduced f]
    (cart : IsPullback h e f g) (F : Sheaf T.smallEtaleTopology (Type (u + 1)))
    (U : X.Etaleᵒᵖ),
    IsIso ((AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g cart F).hom.app U))

end AlgebraicGeometry.Scheme
