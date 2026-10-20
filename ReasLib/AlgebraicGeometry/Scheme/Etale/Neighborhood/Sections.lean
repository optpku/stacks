/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.Algebra.Category.CommRingCat.ULift
public import ReasLib.AlgebraicGeometry.Scheme.Etale.Neighborhood

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary

/-- The functor sending an elementary étale neighborhood to its underlying scheme. -/
def toScheme (S : Scheme.{u}) (s : S) : Elementary S s ⥤ Scheme.{u} :=
  ObjectProperty.ι (fun U : EtaleNeighborhood S s ↦ U.IsElementary) ⋙
    CategoryOfElements.π
      (Etale.forget S ⋙ FunctorToTypes.fromOverFunctor Scheme.forget s) ⋙
    Etale.forget S ⋙ Over.forget S

/-- The object action of `toScheme` forgets to the scheme underlying an elementary étale
neighborhood. -/
@[simp]
theorem toScheme_obj (S : Scheme.{u}) (s : S) (U : Elementary S s) :
    (toScheme S s).obj U = U.obj.toEtale.left := sorry

/-- The morphism action of `toScheme` forgets to the underlying scheme morphism. -/
@[simp]
theorem toScheme_map (S : Scheme.{u}) (s : S) {U V : Elementary S s} (f : U ⟶ V) :
    (toScheme S s).map f =
      (EtaleNeighborhood.Hom.toEtaleHom f.hom).left := sorry

/-- The filtered diagram of global-section rings of elementary étale neighborhoods, with
hom universes and section rings lifted to a common universe. -/
def sections (S : Scheme.{u}) (s : S) :
    ULiftHom.{u + 1} ((Elementary S s)ᵒᵖ) ⥤ CommRingCat.{u + 1} :=
  ULiftHom.down ⋙ (toScheme S s).op ⋙ Scheme.Γ ⋙
    CommRingCat.universeLift.{u, u + 1}

/-- At an elementary étale neighborhood `U`, the sections diagram is the universe lift of
`Γ(U.obj.toEtale.left, ⊤)`. -/
theorem sections_obj (S : Scheme.{u}) (s : S) (U : Elementary S s) :
    (sections S s).obj (ULiftHom.objUp (Opposite.op U)) =
      (CommRingCat.universeLift.{u, u + 1}).obj
        (Scheme.Γ.obj (Opposite.op U.obj.toEtale.left)) := sorry

/-- A pointed map `U ⟶ V` induces the contravariant restriction map from the section ring
of `V` to that of `U`. -/
theorem sections_map (S : Scheme.{u}) (s : S) {U V : Elementary S s} (f : U ⟶ V) :
    (sections S s).map (ULiftHom.up.map f.op) =
      (CommRingCat.universeLift.{u, u + 1}).map
        (Scheme.Γ.map (EtaleNeighborhood.Hom.toEtaleHom f.hom).left.op) := sorry

end AlgebraicGeometry.Scheme.EtaleNeighborhood.Elementary
