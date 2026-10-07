module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.OpenFlat

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace AlgebraicGeometry.Scheme

/- Lemma 59.87.4 -/
@[stacks 0EZZ] #check
  (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_openFlat_sepClosed :
    ∀ {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
      [Flat f], IsOpenMap f.base → (h_cart : IsPullback h e f g) →
      (∀ s : S, IsSepClosed (S.residueField s)) →
      AlgebraicGeometry.Scheme.Etale.HasFiniteOpenDecomposition X →
      AlgebraicGeometry.Scheme.Hom.HasConnectedFiberOpens f →
      (F : Sheaf T.smallEtaleTopology (Type (u + 1))) →
      IsIso (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g h_cart F))

#check (AlgebraicGeometry.Scheme.Etale.HasFiniteOpenDecomposition : Scheme.{u} → Prop)

#check (AlgebraicGeometry.Scheme.Etale.hasFiniteOpenDecomposition_of_normalIntegral :
  ∀ (X : Scheme.{u}) [IsIntegral X], X.isNormal →
    [IsSepClosed X.functionField] →
    AlgebraicGeometry.Scheme.Etale.HasFiniteOpenDecomposition X)

#check (AlgebraicGeometry.Scheme.Hom.HasConnectedFiberOpens :
  ∀ {X S : Scheme.{u}}, (X ⟶ S) → Prop)

#check (AlgebraicGeometry.Scheme.Hom.hasConnectedFiberOpens_of_irreducible :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S),
    (∀ s : S, IsEmpty (f.fiber s) ∨ IrreducibleSpace (f.fiber s)) →
    AlgebraicGeometry.Scheme.Hom.HasConnectedFiberOpens f)

#check (AlgebraicGeometry.Scheme.Etale.BaseChange.setMap_isIso_of_openFlat_sepClosed_app :
  ∀ {X Y S T : Scheme.{u}} (f : X ⟶ S) (h : Y ⟶ X) (e : Y ⟶ T) (g : T ⟶ S)
    [Flat f], IsOpenMap f.base → (h_cart : IsPullback h e f g) →
    (∀ s : S, IsSepClosed (S.residueField s)) →
    AlgebraicGeometry.Scheme.Etale.HasFiniteOpenDecomposition X →
    AlgebraicGeometry.Scheme.Hom.HasConnectedFiberOpens f →
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) → (U : X.Etaleᵒᵖ) →
    IsIso ((AlgebraicGeometry.Scheme.Etale.BaseChange.setMap f h e g h_cart F).hom.app U))

end AlgebraicGeometry.Scheme
