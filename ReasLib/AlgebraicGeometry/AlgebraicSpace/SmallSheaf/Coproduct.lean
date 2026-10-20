module

public import ReasLib.AlgebraicGeometry.AlgebraicSpace.SmallSheaf
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Coproduct

/-!
# Maps from algebraic-space coproducts to small fppf sheaves

Maps from the summands of a small family to an fppf sheaf extend by amalgamating
sections over the open-and-closed pieces of a coproduct section.
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry.AlgebraicSpace

variable {I : Type v} {S : Scheme.{u}} [Small.{u} I]

/-- The morphism `toSmallSheaf (coproduct G) ⟶ P` induced by a family of morphisms from the
summands into a sheaf. -/
def coproductToSmallSheafDesc {G : I → AlgebraicSpace S}
    {P : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (p : ∀ i, toSmallSheaf (G i) ⟶ P) :
    toSmallSheaf (coproduct G) ⟶ P :=
  ObjectProperty.homMk
    { app T := ↾fun s ↦
        (P.property.amalgamateOfArrows
            (fun i : Shrink.{u} I ↦ Over.homMk (s.piece i).ι rfl)
            (CoproductSection.ofArrows_mem s)
            (fun i ↦ ↾fun (_ : PUnit.{u + 1}) ↦
              (p ((equivShrink.{u} I).symm i)).hom.app
                (op (Over.mk ((s.piece i).ι ≫ (unop T).hom)))
                (s.summandSection i))
            sorry)
          PUnit.unit
      naturality := sorry }

/-- Postcomposing a coproduct inclusion with `coproductToSmallSheafDesc p` recovers `p`. -/
theorem coproductToSmallSheafDesc_comp {G : I → AlgebraicSpace S}
    {P : Sheaf (Scheme.fppfTopology.over S) (Type u)}
    (p : ∀ i, toSmallSheaf (G i) ⟶ P) (i : I) :
    toSmallSheafMap (coproductι G i) ≫ coproductToSmallSheafDesc p = p i :=
  sorry

end AlgebraicGeometry.AlgebraicSpace
