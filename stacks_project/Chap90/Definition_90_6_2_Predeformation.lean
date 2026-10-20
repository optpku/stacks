module

public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation

/-!
# Predeformation categories over `ArtinianLocalAlgCat`

A predeformation category is a category cofibered in groupoids over `C_Λ` whose
fibre over the residue field `k` is equivalent to a point: it is nonempty and
has a unique morphism between any two objects.
-/

@[expose] public section

open CategoryTheory

universe u v w

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (ArtinianLocalAlgCat.residue Λ k : ArtinianLocalAlgCat Λ k)
#check (ArtinianLocalAlgCat.residue_carrier Λ k :
  (ArtinianLocalAlgCat.residue Λ k).carrier = k)

variable {Λ k}
variable {F : Type v} [Category.{w} F]

namespace CategoryTheory.Functor

#check (IsPredeformationCategory :
  (F ⥤ ArtinianLocalAlgCat Λ k) → Prop)
#check (instIsPredeformationCategoryId (Λ := Λ) (k := k) :
  IsPredeformationCategory (𝟭 (ArtinianLocalAlgCat Λ k)))
#check (isPredeformationCategory_spec :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k),
    IsPredeformationCategory p ↔
      IsFibered.InGroupoids p.op ∧
        Nonempty (p.Fiber (ArtinianLocalAlgCat.residue Λ k)) ∧
          ∀ x y : p.Fiber (ArtinianLocalAlgCat.residue Λ k),
            Nonempty (x ⟶ y) ∧ Subsingleton (x ⟶ y))
#check (isPredeformationCategory_iff_equiv_punit :
  ∀ (p : F ⥤ ArtinianLocalAlgCat Λ k),
    IsPredeformationCategory p ↔
      IsFibered.InGroupoids p.op ∧
        Nonempty (p.Fiber (ArtinianLocalAlgCat.residue Λ k) ≌ Discrete PUnit))

variable {G : Type v} [Category.{w} G]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) (q : G ⥤ ArtinianLocalAlgCat Λ k)
variable [IsPredeformationCategory p] [IsPredeformationCategory q]

#check (CategoryTheory.Functor.PredeformationMorphism p q : Type (max v w))

end CategoryTheory.Functor
