module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
public import Mathlib.AlgebraicGeometry.Restrict
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.RingTheory.GradedAlgebra.RingHom
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Graded.Multiplication
public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.TensorPower.Graded
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.BasicOpen
public import ReasLib.AlgebraicGeometry.ProjectiveSpectrum.Twist.Sections
public import ReasLib.AlgebraicGeometry.Scheme.Module.Sections
public import ReasLib.RingTheory.GradedAlgebra.GeneratedBy
public import stacks_project.Chap66.Definition_66_18_1_Site
public import stacks_project.Chap66.Lemma_66_29_2_Pullback
public import stacks_project.Chap66.Proposition_66_32_1_Comparison
public import stacks_project.Chap71.Lemma_71_11_11_Triple
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.RelativeProj.Twist

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace
open AlgebraicGeometry.AlgebraicSpace.RelativeProj SheafOfModules.RingedSite
universe u

/- Lemma 71.11.11: twist presentation. -/
#check (AlgebraicGeometry.AlgebraicSpace.RelativeProj.Twist :
    {S : Scheme.{u}} → {X : AlgebraicSpace S} →
    (𝒜 : GradedAlgebraSheaf.{u + 1, u} (commStructureSheafLift X)) →
    DegreePieces 𝒜 → Type (u + 2))
