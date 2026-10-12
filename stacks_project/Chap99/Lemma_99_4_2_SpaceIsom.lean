/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import stacks_project.Chap99.Lemma_99_3_3_SpaceHom
public import stacks_project.Chap99.Lemma_99_4_1_Functor

/-!
# Space-level invertible Hom pairs of quasi-coherent modules

This module cuts the space-level Hom pairs of Situation 99.3.1 down to those
pairs `(h, u)` for which `u : F_T ⟶ G_T` is an `𝒪_{X_T}`-module isomorphism.
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open CategoryTheory.Limits Opposite

noncomputable section

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} {X B : AlgebraicSpace S}

/-- A pair `(h, u)` consisting of a morphism `h : T ⟶ B` and an
`𝒪_{X_T}`-module isomorphism `u : F_T ⟶ G_T` on `X_T = X ×_{B,h} T`. -/
structure SpaceIsom (f : X ⟶ B) (F G : X.Modules) (T : AlgebraicSpace S) :
    Type (u + 1) extends SpaceHom f F G T where
  /-- The module map `F_T ⟶ G_T` is an isomorphism. -/
  isIso : IsIso map

namespace SpaceIsom

/-- Package a morphism `h : T ⟶ B` and an invertible `𝒪_{X_T}`-module map as a
space-level Isom pair. -/
def of {T : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules} (h : T ⟶ B)
    (u : spaceBaseChangeModule f h F ⟶ spaceBaseChangeModule f h G)
    (hu : IsIso u) : SpaceIsom f F G T where
  toSpaceHom := SpaceHom.of h u
  isIso := hu

/-- A space-level Isom pair is a Hom pair whose module map is an isomorphism. -/
theorem spec {T : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (q : SpaceIsom f F G T) :
    q.hom = q.toSpaceHom.hom ∧ q.map = q.toSpaceHom.map ∧ IsIso q.map :=
  sorry

/-- The module map of a space-level Isom pair is an isomorphism. -/
theorem isIso_map {T : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (q : SpaceIsom f F G T) : IsIso q.map :=
  sorry

/-- A Hom pair underlies some Isom pair if and only if its module map is an
isomorphism. -/
theorem exists_toSpaceHom_iff {T : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (p : SpaceHom f F G T) :
    (∃ q : SpaceIsom f F G T, q.toSpaceHom = p) ↔ IsIso p.map :=
  sorry

end SpaceIsom

/-- Restriction of an invertible `𝒪_{X_T}`-module map along `X_{T'} ⟶ X_T`
remains invertible. -/
theorem spaceBaseChangeHom_isIso {T T' : AlgebraicSpace S} (f : X ⟶ B)
    (F G : X.Modules) (h : T ⟶ B) (a : T' ⟶ T)
    {u : spaceBaseChangeModule f h F ⟶ spaceBaseChangeModule f h G}
    (hu : IsIso u) : IsIso (spaceBaseChangeHom f F G h a u) :=
  sorry

namespace SpaceIsom

/-- Pull back an invertible pair `(h, u)` along `a : T' ⟶ T`, sending it to
`(h ∘ a, a^* u)`. -/
def pullback {T T' : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (p : SpaceIsom f F G T) (a : T' ⟶ T) : SpaceIsom f F G T' where
  toSpaceHom := p.toSpaceHom.pullback a
  isIso := spaceBaseChangeHom_isIso f F G p.hom a p.isIso

/-- The morphism of a pulled-back invertible pair is the composite `a ≫ p.hom`. -/
theorem pullback_hom {T T' : AlgebraicSpace S} {f : X ⟶ B} {F G : X.Modules}
    (p : SpaceIsom f F G T) (a : T' ⟶ T) :
    (p.pullback a).hom = a ≫ p.hom :=
  sorry

/-- Convert an Isom-functor section over a scheme `σ` over `B` into a space-level
invertible pair with structural morphism `σ.hom`. -/
def ofScheme {f : X ⟶ B} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    {σ : SchemeOver B} (u : (isomFunctor f F G).obj (op σ)) :
    SpaceIsom f F G (ofOver σ.left) :=
  of σ.hom u.1 u.2

/-- Recover an Isom-functor section from a space-level invertible pair over
`ofOver σ.left` whose structural morphism is `σ.hom`. -/
def toScheme {f : X ⟶ B} {F G : X.Modules} [F.IsQuasicoherent] [G.IsQuasicoherent]
    {σ : SchemeOver B} (p : SpaceIsom f F G (ofOver σ.left))
    (hp : p.hom = σ.hom) : (isomFunctor f F G).obj (op σ) :=
  ⟨SpaceHom.toScheme p.toSpaceHom hp, sorry⟩

end SpaceIsom

end AlgebraicGeometry.AlgebraicSpace.Modules
