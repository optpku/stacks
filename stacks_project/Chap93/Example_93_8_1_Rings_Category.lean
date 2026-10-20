/-
Copyright (c) 2026 Zichen Wang, Zaiwen Wen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zichen Wang, Zaiwen Wen
-/

module

public import ReasLib.AlgebraicGeometry.FormalDeformation.FlatAlgebra
public import ReasLib.AlgebraicGeometry.FormalDeformation.Predeformation

/-!
# Category of flat algebras over `ArtinianLocalAlgCat`

The canonical category, base-change maps, projection, and residue slice.
-/

@[expose] public section

open CategoryTheory Functor

universe u

variable (Λ k : Type u) [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]

#check (FlatAlgebraCat Λ k : Type (u + 1))
#check (FlatAlgebraCat.of :
  ∀ (A : ArtinianLocalAlgCat Λ k) (P : Type u) [CommRing P] [Algebra A.carrier P]
    [Module.Flat A.carrier P], FlatAlgebraCat Λ k)
#check (FlatAlgebraCat.spec :
  ∀ (X : FlatAlgebraCat Λ k), Module.Flat X.base.carrier X.algebra)
#check (FlatAlgebraCat.canonicalTensorMap :
  ∀ {Q P : FlatAlgebraCat Λ k} (f : Q.base ⟶ P.base) (g : Q.algebra →+* P.algebra),
    g.comp (algebraMap Q.base.carrier Q.algebra) =
      (algebraMap P.base.carrier P.algebra).comp f.hom.toRingHom →
    FlatAlgebraCat.tensorAlong f → P.algebra)
#check (FlatAlgebraCat.Hom.spec :
  ∀ {Q P : FlatAlgebraCat Λ k} (f : FlatAlgebraCat.Hom Q P),
    f.toRingHom.comp (algebraMap Q.base.carrier Q.algebra) =
        (algebraMap P.base.carrier P.algebra).comp f.baseHom.hom.toRingHom ∧
      Function.Bijective
        (FlatAlgebraCat.canonicalTensorMap f.baseHom f.toRingHom f.commutes))
#check (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k)
#check (FlatAlgebraCat.instIsFiberedInGroupoids_forget :
  IsFibered.InGroupoids
    (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).op)
#check (FlatAlgebraCat.ofResidue Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P], FlatAlgebraCat Λ k)
#check (FlatAlgebraCat.residueObj Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    (FlatAlgebraCat.forget : FlatAlgebraCat Λ k ⥤ ArtinianLocalAlgCat Λ k).Fiber
      (ArtinianLocalAlgCat.residue Λ k))
#check (FlatAlgebraCat.deformationCategory_spec Λ k :
  ∀ (P : Type u) [CommRing P] [Algebra k P],
    FlatAlgebraCat.deformationCategory Λ k P =
      Over (Fiber.fiberInclusion.obj (FlatAlgebraCat.residueObj Λ k P)))
