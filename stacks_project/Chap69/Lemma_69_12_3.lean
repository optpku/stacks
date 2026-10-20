module

public import ReasLib.Algebra.Category.ModuleCat.Sheaf.RingedSite.Coherent.Closure
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Noetherian
public import ReasLib.AlgebraicGeometry.AlgebraicSpace.Module.Coherent.Category
import StacksCheckRecall

@[expose] public section

open AlgebraicGeometry AlgebraicGeometry.AlgebraicSpace CategoryTheory Limits ObjectProperty

universe u

namespace AlgebraicGeometry.AlgebraicSpace.Modules

variable {S : Scheme.{u}} (X : AlgebraicSpace S) [IsLocallyNoetherian X]

/- Lemma 69.12.3: coherent modules on a locally Noetherian algebraic space over a scheme
form an abelian category. The kernel and cokernel of every morphism between coherent modules
are coherent, and any extension of coherent modules is coherent. These closure properties
are packaged by the weak Serre class of coherent modules. -/
@[stacks 07UC]
#check (SheafOfModules.isCoherent.isWeakSerreClass :
  CategoryTheory.ObjectProperty.IsWeakSerreClass (SheafOfModules.isCoherent (structureSheaf X)))

/- The kernel of a morphism between coherent modules is coherent. -/
#check (SheafOfModules.IsCoherent.kernel :
  ∀ {F G : X.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent],
    (kernel f).IsCoherent)

/- The cokernel of a morphism between coherent modules is coherent. -/
#check (SheafOfModules.IsCoherent.cokernel :
  ∀ {F G : X.Modules} (f : F ⟶ G) [F.IsCoherent] [G.IsCoherent],
    (cokernel f).IsCoherent)

/- In a short exact sequence of modules, coherence of the outer terms implies coherence of
the middle term. -/
#check (SheafOfModules.IsCoherent.middle_of_shortExact :
  ∀ {sc : ShortComplex X.Modules}, sc.ShortExact →
    ∀ [sc.X₁.IsCoherent] [sc.X₃.IsCoherent], sc.X₂.IsCoherent)

/- Coherent modules form an abelian category. -/
#check
  (CategoryTheory.ObjectProperty.instAbelianFullSubcategoryOfContainsZeroOfIsClosedUnderKernelsOfIsClosedUnderCokernelsOfIsClosedUnderFiniteProducts
    (P := SheafOfModules.isCoherent (structureSheaf X)) :
      Abelian (SheafOfModules.isCoherent (structureSheaf X)).FullSubcategory)

end AlgebraicGeometry.AlgebraicSpace.Modules
