module

public import ReasLib.CategoryTheory.Bicategory.Pseudofunctor.OppositeLocallyDiscrete
public import ReasLib.CategoryTheory.Fibered.Cleavage.ReindexIso

@[expose] public section

/-!
# Coherence for the pseudofunctor associated to a cleavage

These are the three proof-valued obligations needed to assemble the chosen reindexing
functors and their canonical comparison isomorphisms into a pseudofunctor.
-/

universe v₁ v₂ u₁ u₂

namespace CategoryTheory

open Functor
open Opposite
open scoped CategoryTheory.Bicategory

variable {C : Type u₁} [Category.{v₁} C]
variable {S : Type u₂} [Category.{v₂} S]

namespace Functor.Cleavage

variable {p : S ⥤ C} (χ : p.Cleavage)

/-- The associativity coherence for the pseudofunctor of fibers. -/
theorem toPseudofunctor.map₂.associator
    {U V W X : Cᵒᵖ} (f : U ⟶ V) (g : V ⟶ W) (h : W ⟶ X) :
    (Cat.Hom.isoMk (Reindex.compIso χ (f ≫ g).unop h.unop)).hom ≫
        (Cat.Hom.isoMk (Reindex.compIso χ f.unop g.unop)).hom ▷
            ((h.unop)⁎[χ]).toCatHom ≫
          (α_ (((f.unop)⁎[χ]).toCatHom) (((g.unop)⁎[χ]).toCatHom)
            (((h.unop)⁎[χ]).toCatHom)).hom ≫
            ((f.unop)⁎[χ]).toCatHom ◁
              (Cat.Hom.isoMk (Reindex.compIso χ g.unop h.unop)).inv ≫
              (Cat.Hom.isoMk (Reindex.compIso χ f.unop (g ≫ h).unop)).inv =
      eqToHom (congrArg (fun k ↦ ((k.unop)⁎[χ]).toCatHom)
        (Category.assoc f g h)) := sorry
/- Proof strategy: use `Cat.Hom₂.ext` objectwise and postcompose with the chosen cartesian
arrow. Successively rewrite with `Reindex.compIsoApp.hom.fac`, its inverse orientation, and
`reindexMap.fac`; the remaining equality is transport along `Category.assoc`. -/

/-- The left-unit coherence for the pseudofunctor of fibers. -/
theorem toPseudofunctor.map₂.leftUnitor
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk (Reindex.compIso χ (𝟙 U).unop f.unop)).hom ≫
        (Cat.Hom.isoMk ((Reindex.idIso χ (unop U)).symm)).hom ▷
            ((f.unop)⁎[χ]).toCatHom ≫
          (λ_ (((f.unop)⁎[χ]).toCatHom)).hom =
      eqToHom (congrArg (fun k ↦ ((k.unop)⁎[χ]).toCatHom)
        (Category.id_comp f)) := sorry
/- Proof strategy: use `Cat.Hom₂.ext` and `cartesianHom.ext`; after postcomposition,
`reindexMap.fac`, `Reindex.idIsoApp.inv.eq_cartesianHom`, and
`Reindex.compIsoApp.hom.fac` identify both sides with the same chosen pullback arrow. -/

/-- The right-unit coherence for the pseudofunctor of fibers. -/
theorem toPseudofunctor.map₂.rightUnitor
    {U V : Cᵒᵖ} (f : U ⟶ V) :
    (Cat.Hom.isoMk (Reindex.compIso χ f.unop (𝟙 V).unop)).hom ≫
        ((f.unop)⁎[χ]).toCatHom ◁
          (Cat.Hom.isoMk ((Reindex.idIso χ (unop V)).symm)).hom ≫
          (ρ_ (((f.unop)⁎[χ]).toCatHom)).hom =
      eqToHom (congrArg (fun k ↦ ((k.unop)⁎[χ]).toCatHom)
        (Category.comp_id f)) := sorry
/- Proof strategy: argue as for the left unit, now using the right-whiskered unit component.
The factorization API reduces both sides to the cartesian arrow over
`𝟙 (unop V) ≫ f.unop`, and `Category.comp_id` supplies the final transport. -/

end Functor.Cleavage

end CategoryTheory
