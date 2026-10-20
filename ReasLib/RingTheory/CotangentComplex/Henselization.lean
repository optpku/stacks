module

public import ReasLib.RingTheory.CotangentComplex.Vanishing

/-!
# Cotangent complexes and henselization

The canonical transitivity maps identify cotangent complexes after henselization
or strict henselization with derived scalar extensions.
-/

@[expose] public section

open CategoryTheory

universe u

namespace Algebra.CotangentComplex

/-- If `Bh` is a henselization of the local ring `B`, the canonical map
`tensor A B Bh ⟶ derived A Bh` is an isomorphism. -/
instance tensorMap_isIso_of_isHenselization (A B Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Bh]
    [IsLocalRing B] [Algebra A B] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [IsScalarTower A B Bh] :
    IsIso (tensorMap A B Bh) :=
  sorry

/-- If `Ah` is a henselization of the local ring `A`, the canonical map
`derived A Bh ⟶ derived Ah Bh` is an isomorphism. -/
instance toRelativeMap_isIso_of_isHenselization (A Ah Bh : Type u)
    [CommRing A] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [Algebra A Ah] [IsHenselizationOf A Ah]
    [Algebra Ah Bh] [Algebra A Bh] [IsScalarTower A Ah Bh] :
    IsIso (toRelativeMap A Ah Bh) :=
  sorry

/-- Under henselization of a local homomorphism of local rings, the objects
`derived Ah Bh` and `tensor A B Bh` are isomorphic in `D(Bh)`. -/
theorem isIsomorphic_derived_tensor_of_isHenselization (A B Ah Bh : Type u)
    [CommRing A] [CommRing B] [CommRing Ah] [CommRing Bh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ah] [IsHenselizationOf A Ah] [Algebra B Bh] [IsHenselizationOf B Bh]
    [Algebra A Bh] [Algebra Ah Bh] [IsScalarTower A B Bh] [IsScalarTower A Ah Bh] :
    IsIsomorphic (derived Ah Bh) (tensor A B Bh) :=
  sorry

/-- If `Bsh` is a strict henselization of the local ring `B`, the canonical map
`tensor A B Bsh ⟶ derived A Bsh` is an isomorphism. -/
instance tensorMap_isIso_of_isStrictHenselization (A B Bsh : Type u)
    [CommRing A] [CommRing B] [CommRing Bsh]
    [IsLocalRing B] [Algebra A B] [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    [Algebra A Bsh] [IsScalarTower A B Bsh] :
    IsIso (tensorMap A B Bsh) :=
  sorry

/-- If `Ash` is a strict henselization of the local ring `A`, the canonical map
`derived A Bsh ⟶ derived Ash Bsh` is an isomorphism. -/
instance toRelativeMap_isIso_of_isStrictHenselization (A Ash Bsh : Type u)
    [CommRing A] [CommRing Ash] [CommRing Bsh]
    [IsLocalRing A] [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra Ash Bsh] [Algebra A Bsh] [IsScalarTower A Ash Bsh] :
    IsIso (toRelativeMap A Ash Bsh) :=
  sorry

/-- Under strict henselization of a local homomorphism of local rings, the objects
`derived Ash Bsh` and `tensor A B Bsh` are isomorphic in `D(Bsh)`. -/
theorem isIsomorphic_derived_tensor_of_isStrictHenselization (A B Ash Bsh : Type u)
    [CommRing A] [CommRing B] [CommRing Ash] [CommRing Bsh]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra A Ash] [IsStrictHenselizationOf A Ash]
    [Algebra B Bsh] [IsStrictHenselizationOf B Bsh]
    [Algebra A Bsh] [Algebra Ash Bsh]
    [IsScalarTower A B Bsh] [IsScalarTower A Ash Bsh] :
    IsIsomorphic (derived Ash Bsh) (tensor A B Bsh) :=
  sorry

end Algebra.CotangentComplex
