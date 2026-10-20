module

public import ReasLib.AlgebraicGeometry.Scheme.Sites.Etale.Affine.Colimit
import StacksCheckRecall

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

universe u

/- Lemma 59.51.2: the affine etale site of the limit of a directed inverse
system of schemes with affine transition morphisms is the explicit colimit of
the affine etale sites of the stages. -/
@[stacks 0EYL] #check
  (AlgebraicGeometry.Scheme.AffineEtaleColimit.isColimitSite :
    ∀ {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (D : OrderDual I ⥤ Scheme.{u})
      [∀ {i j : I} (hij : i ≤ j), IsAffineHom (D.map (homOfLE hij))]
      (c : Cone D) (hc : IsLimit c),
      ∃ e : (AlgebraicGeometry.Scheme.AffineEtaleColimit.diagram D).ColimitCategory ≌
          c.pt.AffineEtale,
        e.functor.inducedTopology (Scheme.AffineEtale.topology c.pt) =
          (AlgebraicGeometry.Scheme.AffineEtaleColimit.diagram D).colimitTopology)
