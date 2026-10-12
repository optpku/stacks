/-
Released under Apache 2.0 license as described in the file LICENSE.
Statement formalization authors: ReasBook team
Proof formalization authors: ReasBook team
-/

module

public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.CategoryTheory.IsomorphismClasses
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.CategoryTheory.Sites.Whiskering
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Basic
public import Mathlib.RepresentationTheory.Homological.ContCohomology.Functoriality
public import Mathlib.RingTheory.AdicCompletion.Basic
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology
public import Mathlib.Topology.Algebra.OpenSubgroup
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.AlgebraicGeometry.Sites.ElladicCohomology

/-!
# Completed Galois sheaves on the small pro-étale site of a point

Given a geometric point of `Spec k`, the étale Galois correspondence supplies
locally constant sheaves on `Spec k_étale`. Pulling back along `ε` and taking
the inverse limit produces the completed Galois sheaf `underline{M}^∧` on
`Spec k_proétale`.
-/

@[expose] public section
open CategoryTheory
open AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section
universe u
namespace AlgebraicGeometry.Scheme.ProEt
/-- Grothendieck-abelian structure on abelian sheaves on the small pro-étale
site after the `u ↦ u+1` ulift, matching `ellAdicSheaf`. -/
instance isGrothendieckAbelian_sheaf_proEt (S : Scheme.{u}) :
    IsGrothendieckAbelian.{u + 1}
      (Sheaf (topology S) AddCommGrpCat.{u + 1}) :=
  by
    have : EssentiallySmall.{u + 1} S.ProEt := inferInstance
    exact Sheaf.isGrothendieckAbelian_of_essentiallySmall
      (topology S) AddCommGrpCat.{u + 1}

/-- Pro-étale cohomology of an abelian sheaf on the small pro-étale site,
after the ulift used by `EllAdicCohomology`. -/
public def proEtaleCohomology (S : Scheme.{u})
    (F : Sheaf (topology S) AddCommGrpCat.{u}) (n : ℕ) : AddCommGrpCat.{u + 1} :=
  AddCommGrpCat.of
    (((sheafCompose (topology S) AddCommGrpCat.uliftFunctor.{u + 1, u}).obj F).H n)

/-- The map on pro-étale cohomology induced by a morphism of abelian sheaves. -/
public def proEtaleCohomologyMap {S : Scheme.{u}}
    {F G : Sheaf (topology S) AddCommGrpCat.{u}} (f : F ⟶ G) (n : ℕ) :
    proEtaleCohomology S F n ⟶ proEtaleCohomology S G n :=
  AddCommGrpCat.ofHom
    (Sheaf.H.map
      ((sheafCompose (topology S) AddCommGrpCat.uliftFunctor.{u + 1, u}).map f) n)
end AlgebraicGeometry.Scheme.ProEt

end
