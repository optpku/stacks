module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.GroupScheme.PseudoTorsor
public import stacks_project.Chap39.Definition_39_11_1_PseudoTorsor

@[expose] public section

open CategoryTheory
open scoped MonObj ModObj

universe u

variable (S : AlgebraicGeometry.Scheme.{u})
  (G : Grp (Over S)) (X : Mod (Over S) G.X)

/- Lemma 39.11.2 (1): The scheme `X` is a pseudo `G`-torsor if and only if, for
every scheme `T` over `S`, the action of `G(T)` on `X(T)` is simply transitive
whenever `X(T)` is nonempty. -/
@[stacks 0499] #check
  (CategoryTheory.Mod.isPseudoTorsor_iff_forall_existsUnique_smul X :
    CategoryTheory.Mod.IsPseudoTorsor X ↔
      ∀ (T : Over S) (x y : T ⟶ X.X), ∃! g : T ⟶ G.X, g • x = y)

variable [CategoryTheory.Mod.IsPseudoTorsor X]

/- Lemma 39.11.2 (2): A pseudo `G`-torsor `X` is trivial if and only if the
morphism `X.X.hom : X.X.left ⟶ S` admits a section. -/
@[stacks 0499] #check
  (AlgebraicGeometry.GroupScheme.isTrivial_iff_exists_section S G X :
    CategoryTheory.Mod.IsTrivial X ↔
      ∃ s : S ⟶ X.X.left, s ≫ X.X.hom = 𝟙 S)
