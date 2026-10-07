module

public import stacks_project.Chap90.Lemma_90_19_9_Module
import StacksCheckRecall

/-!
# Lemma 90.19.9

If `p : F ⥤ ArtinianLocalAlgCat Λ k` is cofibered in groupoids and satisfies
(RS), and `x0` is a residue-fibre object, then `Inf_{x0}(F)` equals
`T_id Aut(x0)` as sets, and therefore carries the natural `k`-vector space
structure of Lemma 90.19.7 in which addition agrees with composition of
automorphisms.
-/

@[expose] public section

open CategoryTheory hiding Linear
open CategoryTheory.Functor
open ArtinianLocalAlgCat
open Fiber

universe u v w

variable {Λ k : Type u} [CommRing Λ] [IsNoetherianRing Λ] [Field k] [Algebra Λ k]
  [Module.Finite Λ k]
variable {F : Type v} [Category.{w} F]
variable (p : F ⥤ ArtinianLocalAlgCat Λ k) [HasRimSchlessinger p]
variable (x0 : p.Fiber (residue Λ k))
variable (x0' : p.Fiber (dualNumber Λ k))
variable (φ : fiberInclusion.obj x0 ⟶ fiberInclusion.obj x0')
variable [p.IsStronglyCocartesian (residueToDualNumber Λ k) φ]

/- Lemma 90.19.9 (1): Let F be a category cofibered in groupoids over C_Λ
satisfying (RS). Let x0 be an object of F(k). Then Inf_{x0}(F) is equal as a
set to T_id Aut(x0), via infinitesimalAutomorphismsAtMulEquiv. -/
@[stacks 06JX]
#check infinitesimalAutomorphismsAtMulEquiv

/- Lemma 90.19.9 (2): Inf_{x0}(F) has a natural k-vector space structure such
that addition agrees with composition of automorphisms. -/
@[stacks 06JX]
#check (instModule_infinitesimalAutomorphismsAt p x0 x0' φ :
    Module k (infinitesimalAutomorphismsAt p x0 x0' φ))

/- Lemma 90.19.9 (3): addition in Inf_{x0}(F) agrees with composition of
automorphisms. -/
@[stacks 06JX]
#check infinitesimalAutomorphismsAt_add_eq_mul
