module

import StacksCheckRecall
public import stacks_project.Chap93.Example_93_8_1_Rings_Category
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Localization
public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra.Henselization

/-!
# Deformation category of a ring

The category of flat algebras over Artinian local bases and its residue-object slice.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

/- Example 93.8.1 (Rings) (1)
An object is a pair (A, P) with A in C_Λ and P a flat commutative A-algebra.
A morphism (f, g) : (B, Q) ⟶ (A, P) has a base arrow f and an f-linear ring
map g whose canonical tensor lift A ⊗[B] Q → P is bijective. The reversed
tensor order is the canonical commutative convention for Q ⊗[B] A ≅ P.
-/
@[stacks 0DY1] #check (FlatAlgebraCat Λ k : Type (u + 1))

#check (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)
#check (FlatAlgebraCat.forget_obj :
  ∀ (X : FlatAlgebraCat Λ k), FlatAlgebraCat.forget.obj X = X.base)
#check (FlatAlgebraCat.forget_map :
  ∀ {Q P : FlatAlgebraCat Λ k} (f : Q ⟶ P), FlatAlgebraCat.forget.map f = f.baseHom)

/- Example 93.8.1 (Rings) (1), cofiberedness
The projection sends (A, P) to A and (f, g) to f and is cofibered in groupoids.
-/
@[stacks 0DY1] #check (FlatAlgebraCat.instIsFiberedInGroupoids_forget :
  IsFibered.InGroupoids
    (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).op)

/- Example 93.8.1 (Rings) (2)
For a commutative k-algebra P, the residue-fiber object x₀ is the pair (k, P).
The deformation category Def_P = F_{x₀} consists of arrows to this residue
object, with morphisms the commuting triangles.
-/
@[stacks 0DY1] #check (FlatAlgebraCat.deformationCategory Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P], Type (u + 1))

#check (FlatAlgebraCat.residueObj Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).Fiber
      (ArtinianLocalAlgCat.residue Λ k))
#check (FlatAlgebraCat.residueObj_fiberInclusion Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P) =
      FlatAlgebraCat.ofResidue Λ k P)
#check (FlatAlgebraCat.deformationCategory_spec Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    FlatAlgebraCat.deformationCategory Λ k P =
      Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P)))

/-- The deformation category of a commutative residue-field algebra. -/
abbrev deformationCategory (P : Type u) [CommRing P] [Algebra k P] :=
  FlatAlgebraCat.deformationCategory Λ k P
