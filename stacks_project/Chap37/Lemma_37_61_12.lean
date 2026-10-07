module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Derived.Quasicoherent.Pushforward.StructureSheaf.PerfectClosedImmersion
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.DerivedQCoh

/- Lemma 37.61.12: for a perfect closed immersion `i : Z ⟶ X`, the direct image
`i_*𝒪_Z`, placed in degree zero, is a perfect object of `D(𝒪_X)`. -/
@[stacks 0G2E] #check
  (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardStructureSheaf_isPerfect :
    ∀ {X Z : AlgebraicGeometry.Scheme.{u}} (i : Z ⟶ X)
      [AlgebraicGeometry.IsClosedImmersion i],
      AlgebraicGeometry.LocallyOfType RingHom.IsPerfectRingMap i →
        AlgebraicGeometry.RingedSpace.ModuleDerived.IsPerfect
          (AlgebraicGeometry.Scheme.DerivedQCoh.pushforwardStructureSheaf i).obj)

end AlgebraicGeometry.Scheme.DerivedQCoh
