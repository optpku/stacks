module

public import stacks_project.Chap59.Lemma_59_104_1_EtaleSheafDescent
public import ReasLib.AlgebraicGeometry.Scheme.Sites.H.ChosenPresentation
public import ReasLib.AlgebraicGeometry.Scheme.Sites.ChosenPresentation.Limits
public import Mathlib.CategoryTheory.FiberedCategory.Grothendieck
public import Mathlib.CategoryTheory.Sites.Descent.IsStack

@[expose] public section

open CategoryTheory AlgebraicGeometry
open CategoryTheory.Pseudofunctor

noncomputable section

universe u v

namespace AlgebraicGeometry.Scheme.EtaleSheaf

variable (Schh : ChosenBigHSite.{u, v}) (S : Schh.carrier)

/-- Restriction of the small étale sheaf pseudofunctor to a slice of a chosen big h site. -/
def overPseudofunctor :
    Pseudofunctor (LocallyDiscrete (Over S)ᵒᵖ) Cat :=
  let F := ChosenBigSite.sliceToScheme Schh S
  LocallyDiscrete.mkPseudofunctor
    (fun X ↦ Cat.of (Sheaf (F.obj X.unop).smallEtaleTopology (Type (u + 1))))
    (fun f ↦ (pullback (F.map f.unop)).toCatHom)
    (fun X ↦
      Cat.Hom.isoMk
        ((eqToIso
            (congrArg pullback
              ((congrArg F.map (unop_id)).trans
                (CategoryTheory.Functor.map_id F X.unop))) :
              pullback (F.map (𝟙 X).unop) ≅ pullback (𝟙 (F.obj X.unop))).trans
          (pullbackId (F.obj X.unop))))
    (fun f g ↦
      Cat.Hom.isoMk
        ((eqToIso
            (congrArg pullback
              ((congrArg F.map (unop_comp)).trans
                (CategoryTheory.Functor.map_comp F g.unop f.unop))) :
              pullback (F.map (f ≫ g).unop) ≅
                pullback (F.map g.unop ≫ F.map f.unop)).trans
          (pullbackComp (F.map f.unop) (F.map g.unop)).symm))
    (fun _ _ _ ↦ sorry)
    (fun _ ↦ sorry)
    (fun _ ↦ sorry)

/-- The fibre of `overPseudofunctor` over a slice object is Type-valued small étale sheaves. -/
theorem overPseudofunctor_obj (U : Over S) :
    (overPseudofunctor Schh S).obj (.mk (.op U)) =
      Cat.of
        (Sheaf ((ChosenBigSite.sliceToScheme Schh S).obj U).smallEtaleTopology
          (Type (u + 1))) :=
  sorry

/-- The action of `overPseudofunctor` on a slice morphism is small étale sheaf pullback. -/
theorem overPseudofunctor_map {U V : Over S} (f : U ⟶ V) :
    ((overPseudofunctor Schh S).map f.op.toLoc).toFunctor =
      pullback ((ChosenBigSite.sliceToScheme Schh S).map f) :=
  sorry

/-- The CoGrothendieck projection of étale sheaves over `(Sch/S)_h`. -/
abbrev overForget : CoGrothendieck (overPseudofunctor Schh S) ⥤ Over S :=
  CoGrothendieck.forget (overPseudofunctor Schh S)

/-- The HasFibers fibre of `overForget` over `U` is `Sh(U_étale)`. -/
theorem overFiber_eq (U : Over S) :
    HasFibers.Fib (overForget Schh S) U =
      (overPseudofunctor Schh S).obj ⟨.op U⟩ :=
  sorry

end AlgebraicGeometry.Scheme.EtaleSheaf
