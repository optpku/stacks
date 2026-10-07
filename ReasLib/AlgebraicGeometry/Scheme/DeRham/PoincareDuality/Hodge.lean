module

public import ReasLib.AlgebraicGeometry.Scheme.DeRham.PoincareDuality.Forms
public import ReasLib.AlgebraicGeometry.Scheme.OverField

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.MonoidalCategory
open CategoryTheory.MonoidalClosed TopologicalSpace
open scoped AlgebraicGeometry MonoidalCategory

noncomputable section

universe u

namespace AlgebraicGeometry.Scheme.DeRham

variable {k : Type u} [Field k] (X : AlgebraicGeometry.SchemeOverField k) (d : ℕ)
variable [Nonempty X.left] [Smooth X.hom] [IsProper X.hom]
variable [EquidimensionalSpace X.left]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends X.left.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends X.left.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization X.left.toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.HomotopyTensorDescends
  (Spec (CommRingCat.of k)).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.TensorDescends
  (Spec (CommRingCat.of k)).toRingedSpace]
variable [RingedSpace.ModuleDerived.KFlat.IsLocalization
  (Spec (CommRingCat.of k)).toRingedSpace]
variable [HomotopyCategory.KFlat.HasResolutions X.left.Modules]
variable [RingedSite.Hom.DerivedAdjunction.HasPair
  (RingedSpace.opensRingedSiteHom X.hom.toShHom)]
variable [Functor.Monoidal (RingedSpace.modulePullbackDerived X.hom.toShHom)]
variable [MonoidalClosed
  (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace)]

/-- A nonempty smooth proper equidimensional scheme of dimension `d` over a field
`k` admits a trace on its shifted top Hodge object whose complementary cup-product
pairings are perfect. -/
theorem existsHodgePoincareTrace
    (h_dimension : topologicalKrullDim X.left = d) :
    ∃ t : (pushforwardForm X.hom d)⟦(d : ℤ)⟧ ⟶
        𝟙_ (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace),
      PoincareTrace.IsPerfect X.hom d t := sorry

/-- Any two perfect traces on a nonempty smooth proper equidimensional scheme of
dimension `d` over a field differ by precomposition with a unit of `Γ(X.left, ⊤)`. -/
theorem hodgePoincareTrace_unique
    (h_dimension : topologicalKrullDim X.left = d)
    (t t' : (pushforwardForm X.hom d)⟦(d : ℤ)⟧ ⟶
      𝟙_ (RingedSpace.ModuleDerived (Spec (CommRingCat.of k)).toRingedSpace))
    (ht : PoincareTrace.IsPerfect X.hom d t)
    (ht' : PoincareTrace.IsPerfect X.hom d t') :
    ∃ u : Γ(X.left, ⊤)ˣ, t' = PoincareTrace.unitAction X.hom d u ≫ t := sorry

end AlgebraicGeometry.Scheme.DeRham
