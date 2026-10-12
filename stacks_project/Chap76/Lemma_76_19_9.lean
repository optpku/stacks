/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.CategoryTheory.Limits.Shapes.ZeroObjects
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import ReasLib.AlgebraicGeometry.Scheme.Module.LocallyProjective.Basic
public import stacks_project.Chap76.Lemma_76_19_9_InternalHom

/-!
# Vanishing of H¹ of étale internal Hom on an affine scheme

On an affine scheme, the first étale cohomology of the internal Hom of
associated étale modules vanishes when the source is locally projective.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits
open AlgebraicGeometry.Scheme.Modules
open AlgebraicGeometry.Scheme.AssociatedModule

universe u

namespace AlgebraicGeometry.Scheme.AssociatedModule

/-- Lemma 76.19.9: if `T` is an affine scheme and `F`, `G` are quasi-coherent
`𝒪_T`-modules on the small étale site of `T`, presented as associated étale
modules of quasi-coherent scheme modules, and if `F` is locally projective,
then `H¹(T_étale, etaleInternalHom F G) = 0`. -/
@[stacks 061J]
theorem etaleInternalHom_firstCohomology_isZero
    {T : Scheme.{u}} [IsAffine T] (F G : T.Modules)
    [F.IsQuasicoherent] [G.IsQuasicoherent] [IsLocallyProjective F]
    [HasSheafify (StandardTopology.Small.topology .etale T) AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1}
      (Sheaf (StandardTopology.Small.topology .etale T) AddCommGrpCat.{u + 1})] :
    IsZero
      ((Sheaf.functorH (StandardTopology.Small.topology .etale T) 1).obj
        (etaleInternalHom_toSheaf F G)) :=
  sorry

end AlgebraicGeometry.Scheme.AssociatedModule
