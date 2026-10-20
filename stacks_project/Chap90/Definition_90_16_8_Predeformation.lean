module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation

/-!
# Predeformation categories over `ArtinianLocalAlgCat`

A predeformation category is a category cofibered in groupoids over `C_Λ` whose
fibre over the residue field `k` is equivalent to a point: it is nonempty and
has a unique morphism between any two objects.
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u v w

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (ArtinianLocalAlgCat.residue Λ k : ArtinianLocalAlgCat Λ k)

#check (ArtinianLocalAlgCat.residue_carrier Λ k :
  (ArtinianLocalAlgCat.residue Λ k).carrier = k)

variable {Λ k}
variable {F : Type v} [Category.{w} F]

variable (p : F ⥤ ArtinianLocalAlgCat Λ k)

#check (CategoryTheory.Functor.IsPredeformationCategory p : Prop)

#check (CategoryTheory.Functor.isPredeformationCategory_spec p :
  CategoryTheory.Functor.IsPredeformationCategory p ↔
    CategoryTheory.Functor.IsFibered.InGroupoids p.op ∧
      Nonempty (p.Fiber (ArtinianLocalAlgCat.residue Λ k)) ∧
        ∀ x y : p.Fiber (ArtinianLocalAlgCat.residue Λ k),
          Nonempty (x ⟶ y) ∧ Subsingleton (x ⟶ y))
