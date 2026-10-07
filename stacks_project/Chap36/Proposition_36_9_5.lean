module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.RingedSpace.Module.Derived.Koszul.PrincipalOpen.Quasicoherent
public import stacks_project.Chap36.«36_3_5_1_DerivedQCoh»
public import stacks_project.Chap36.«36_9_4_1_Comparison»

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry
namespace RingedSpace
namespace ModuleDerived
namespace Koszul

/- Proposition 36.9.5: for `X = Spec(A)`,
`U = Scheme.PrincipalOpenCech.openSubset f`, and every
`E : Scheme.DerivedQCoh X`, the canonical map from the colimit of `Hom(Iₑ, E)`
to `H⁰(U, E)` is an isomorphism. -/
@[stacks 08DD] #check
  (AlgebraicGeometry.RingedSpace.ModuleDerived.Koszul.homColimitToOpenH0_isIso :
    ∀ {A : Type u} [CommRing A] {r : ℕ} (f : Fin r → A)
      (E : Scheme.DerivedQCoh (Spec (CommRingCat.of A))),
      IsIso (homColimitToOpenH0 f E.obj))

end Koszul
end ModuleDerived
end RingedSpace
end AlgebraicGeometry
