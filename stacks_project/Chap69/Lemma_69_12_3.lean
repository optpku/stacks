module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import stacks_project.Chap66.Definition_66_24_1_Noetherian
public import stacks_project.Chap67.Definition_67_14_4_IdealSubobject
public import stacks_project.Chap69.Definition_69_12_1_Instances
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]

/- Lemma 69.12.3 (1): the kernel of a morphism between coherent modules on a locally
Noetherian algebraic space is coherent. -/
@[stacks 07UC]
#check (SheafOfModules.IsCoherent.kernel :
  ∀ {F G : X.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent],
    (kernel f).IsCoherent)

/- Lemma 69.12.3 (2): the cokernel of a morphism between coherent modules on a locally
Noetherian algebraic space is coherent. -/
@[stacks 07UC]
#check (SheafOfModules.IsCoherent.cokernel :
  ∀ {F G : X.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent],
    (cokernel f).IsCoherent)

/- Lemma 69.12.3 (3): in a short exact sequence of modules on a locally Noetherian algebraic
space, coherence of the outer terms implies coherence of the middle term. -/
@[stacks 07UC]
#check (SheafOfModules.IsCoherent.middle_of_shortExact :
  ∀ {sc : ShortComplex X.Modules}, sc.ShortExact →
    ∀ [sc.X₁.IsCoherent] [sc.X₃.IsCoherent], sc.X₂.IsCoherent)

/- Lemma 69.12.3 (4): coherent modules on a locally Noetherian algebraic space form an abelian
category. -/
@[stacks 07UC]
#check
  (CategoryTheory.ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
    (P := SheafOfModules.isCoherent (structureSheaf X)) :
      Abelian (SheafOfModules.isCoherent (structureSheaf X)).FullSubcategory)

end AlgebraicGeometry.AlgebraicSpace.Modules
