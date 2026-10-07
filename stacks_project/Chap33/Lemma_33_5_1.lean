module

import StacksCheckRecall
public import ReasLib.AlgebraicGeometry.Scheme.FieldExtension.Stalk.Local

@[expose] public section

open CategoryTheory

universe u

/- Lemma 33.5.1 (1): the map from the source stalk to the stalk at a point of the
field-extension base change is local and faithfully flat. -/
@[stacks 0C4Y] #check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.toSourceMap_isLocal :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      IsLocalHom
        (AlgebraicGeometry.FieldExtension.Stalk.toSourceMap k K f y).hom)

#check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.toSourceMap_faithfullyFlat :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      RingHom.FaithfullyFlat
        (AlgebraicGeometry.FieldExtension.Stalk.toSourceMap k K f y).hom)

/- Lemma 33.5.1 (2): the point prime is the kernel of the residue-tensor map,
and its residue field maps canonically and bijectively to the residue field of the point. -/
@[stacks 0C4Y] #check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.pointPrime_asIdeal :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      AlgebraicGeometry.FieldExtension.Stalk.pointPrimeIdeal k K f y =
        RingHom.ker
          (AlgebraicGeometry.FieldExtension.Stalk.residueTensorMap k K f y).hom)

#check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.pointPrime_residueFieldMap :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      (AlgebraicGeometry.FieldExtension.Stalk.pointPrimeIdeal k K f y).ResidueField →+*
        AlgebraicGeometry.FieldExtension.Stalk.residueField k K f y)

#check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.pointPrime_residueFieldMap_bijective :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      Function.Bijective
        (AlgebraicGeometry.FieldExtension.Stalk.Local.pointPrime_residueFieldMap f y))

/- Lemma 33.5.1 (3): the base-change stalk is the localization of the source-stalk
tensor product at the inverse-image point prime. -/
@[stacks 0C4Y] #check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.stalk_isLocalizationAtPrime :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      IsLocalization.AtPrime
        ((AlgebraicGeometry.FieldExtension.baseChange k K f).presheaf.stalk y)
        (AlgebraicGeometry.FieldExtension.Stalk.Tensor.primeIdeal k K f y))

/- Lemma 33.5.1 (4): quotienting by the extended source maximal ideal gives the
localization of the residue tensor at the point prime. -/
@[stacks 0C4Y] #check
  (AlgebraicGeometry.FieldExtension.Stalk.Local.closedFiber_isLocalizationAtPrime :
    ∀ {k K : Type u} [Field k] [Field K] [Algebra k K]
      {X : AlgebraicGeometry.Scheme.{u}}
      (f : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of k))
      (y : AlgebraicGeometry.FieldExtension.baseChange k K f),
      IsLocalization.AtPrime
        (AlgebraicGeometry.FieldExtension.Stalk.ClosedFiber.quotient k K f y)
        (AlgebraicGeometry.FieldExtension.Stalk.pointPrimeIdeal k K f y))
