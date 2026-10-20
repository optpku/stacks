module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.RimSchlessinger
import StacksCheckRecall

/-!
# Rim-Schlessinger condition for flat algebras

Example 93.8.1 satisfies (RS), so each residue-fibre slice `Def_P` is a deformation
category.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Lemma 93.8.2. Example 93.8.1 satisfies the Rim-Schlessinger condition (RS).
In particular, its residue-fibre slice is a deformation category for every k-algebra P. -/
@[stacks 0DY2] #check (FlatAlgebraCat.instHasRimSchlessinger_forget :
  HasRimSchlessinger (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k))

#check (FlatAlgebraCat.instIsDeformationCategory_deformationCategory :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    IsDeformationCategory
      (Over.forget (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P)) ⋙
        FlatAlgebraCat.forget))
