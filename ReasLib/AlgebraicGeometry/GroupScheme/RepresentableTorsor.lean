module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Grp
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod
public import Mathlib.CategoryTheory.Sites.Canonical
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import ReasLib.AlgebraicGeometry.GroupScheme.Torsor
public import ReasLib.AlgebraicGeometry.Scheme.Sites.Standard.Subcanonical
public import ReasLib.CategoryTheory.Sites.Presheaf.Terminal

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.GroupScheme

/-- The represented action is simply transitive and locally nonempty for the selected
standard topology. -/
def IsSheafTorsor {S : Scheme.{u}} (τ : StandardTopology) (G : Grp (Over S))
    (X : Mod (Over S) G.X) : Prop :=
  Mod.IsPseudoTorsor X ∧
    Presheaf.IsLocallySurjective (τ.overTopology S)
      (terminal.from (yoneda.obj X.X))

/-- The represented-action torsor condition consists of simple transitivity and local
nonemptiness. -/
theorem isSheafTorsor_iff {S : Scheme.{u}} (τ : StandardTopology) (G : Grp (Over S))
    (X : Mod (Over S) G.X) :
    IsSheafTorsor τ G X ↔
      Mod.IsPseudoTorsor X ∧
        Presheaf.IsLocallySurjective (τ.overTopology S)
          (terminal.from (yoneda.obj X.X)) := sorry

namespace IsStandardTorsor

/-- A standard-cover torsor is exactly a pseudo-torsor whose represented scheme is locally
nonempty. -/
theorem iff_isLocallySurjective
    {S : Scheme.{u}} (τ : StandardTopology) (G : Grp (Over S)) (X : Mod (Over S) G.X) :
    IsStandardTorsor G X τ ↔
      Mod.IsPseudoTorsor X ∧
        Presheaf.IsLocallySurjective (τ.overTopology S)
          (terminal.from (yoneda.obj X.X)) := sorry

end IsStandardTorsor

/-- The group-valued Yoneda presheaf of a group scheme is a sheaf for every standard
topology. -/
theorem representableGroup_isSheaf {S : Scheme.{u}} (τ : StandardTopology)
    (G : Grp (Over S)) :
    Presheaf.IsSheaf (τ.overTopology S) (yonedaGrp.obj G) := sorry

/-- The group sheaf represented by a group scheme on the selected standard site. -/
def representableGroup {S : Scheme.{u}} (τ : StandardTopology) (G : Grp (Over S)) :
    Sheaf (τ.overTopology S) GrpCat :=
  ⟨yonedaGrp.obj G, representableGroup_isSheaf τ G⟩

/-- The underlying group-valued presheaf of `representableGroup` is group-valued Yoneda. -/
theorem representableGroup_val {S : Scheme.{u}} (τ : StandardTopology)
    (G : Grp (Over S)) :
    (representableGroup τ G).1 = yonedaGrp.obj G := sorry

/-- Standard-cover local triviality is equivalent to the represented-action torsor
condition on the corresponding standard site. -/
theorem isStandardTorsor_iff_isSheafTorsor {S : Scheme.{u}} (τ : StandardTopology)
    (G : Grp (Over S)) (X : Mod (Over S) G.X) :
    IsStandardTorsor G X τ ↔ IsSheafTorsor τ G X := by
  rw [isSheafTorsor_iff]
  exact IsStandardTorsor.iff_isLocallySurjective τ G X

end AlgebraicGeometry.GroupScheme
