module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.BaseChange.ZMod

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

#check (AlgebraicGeometry.Scheme.Etale.zmodSheafPushforward :
  ∀ {A B : Scheme.{u}} (p : A ⟶ B) (n : ℕ),
    Sheaf A.smallEtaleTopology (ModuleCat.{u} (ZMod n)) ⥤
      Sheaf B.smallEtaleTopology (ModuleCat.{u} (ZMod n)))
