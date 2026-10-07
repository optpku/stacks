module

public import ReasLib.Algebra.Category.ModuleCat.Tor.IntersectionMultiplicity
import StacksCheckRecall

@[expose] public section

open CategoryTheory

noncomputable section

universe u

/- Remark 43.19.5 (1): every Tor module has finite length when the tensor product
of the two nonzero finite modules is supported at the closed point. -/
@[stacks 0B0X] #check
  (CategoryTheory.ModuleCat.Tor.length_ne_top_of_tensorSupport :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
      (M N : ModuleCat.{u} R)
      [Module.Finite R M] [Module.Finite R N]
      [Nontrivial M] [Nontrivial N]
      (_ : Module.support R (ModuleCat.TensorProduct.obj R M N) ⊆
        {IsLocalRing.closedPoint R}) (p : ℕ),
      Module.length R (CategoryTheory.ModuleCat.Tor.obj p M N) ≠ ⊤)

/- Remark 43.19.5 (2): the Tor modules of the two finite modules vanish in all
sufficiently large degrees, so their Euler characteristic is a finite sum. -/
@[stacks 0B0X] #check
  (CategoryTheory.ModuleCat.Tor.eventuallyIsZero_of_regularLocal :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
      (M N : ModuleCat.{u} R)
      [Module.Finite R M] [Module.Finite R N]
      [Nontrivial M] [Nontrivial N]
      (_ : Module.support R (ModuleCat.TensorProduct.obj R M N) ⊆
        {IsLocalRing.closedPoint R}),
      CategoryTheory.ModuleCat.Tor.EventuallyIsZero M N)

/- Remark 43.19.5 (3): the sum of the dimensions of the two module supports is
at most the Krull dimension of the regular local ring. -/
@[stacks 0B0X] #check
  (CategoryTheory.ModuleCat.Tor.supportDim_add_le :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
      (M N : ModuleCat.{u} R)
      [Module.Finite R M] [Module.Finite R N]
      [Nontrivial M] [Nontrivial N]
      (_ : Module.support R (ModuleCat.TensorProduct.obj R M N) ⊆
        {IsLocalRing.closedPoint R}),
      Module.supportDim R M + Module.supportDim R N ≤ ringKrullDim R)

/- Remark 43.19.5 (4): below the expected total support dimension, the Tor Euler
characteristic vanishes. -/
@[stacks 0B0X] #check
  (CategoryTheory.ModuleCat.Tor.eulerCharacteristic_eq_zero_of_supportDim_add_lt :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
      (M N : ModuleCat.{u} R)
      [Module.Finite R M] [Module.Finite R N]
      [Nontrivial M] [Nontrivial N]
      (_ : Module.support R (ModuleCat.TensorProduct.obj R M N) ⊆
        {IsLocalRing.closedPoint R})
      (_ : Module.supportDim R M + Module.supportDim R N < ringKrullDim R),
      CategoryTheory.ModuleCat.Tor.eulerCharacteristic M N = 0)

/- Remark 43.19.5 (5): the Tor Euler characteristic is nonnegative. -/
@[stacks 0B0X] #check
  (CategoryTheory.ModuleCat.Tor.eulerCharacteristic_nonneg :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
      (M N : ModuleCat.{u} R)
      [Module.Finite R M] [Module.Finite R N]
      [Nontrivial M] [Nontrivial N]
      (_ : Module.support R (ModuleCat.TensorProduct.obj R M N) ⊆
        {IsLocalRing.closedPoint R}),
      0 ≤ CategoryTheory.ModuleCat.Tor.eulerCharacteristic M N)

/- Remark 43.19.5 (6): when the regular local ring contains a field and the
support dimensions have the expected sum, the Tor Euler characteristic is positive.
Without the field hypothesis, this strict positivity remains conjectural. -/
@[stacks 0B0X] #check
  (CategoryTheory.ModuleCat.Tor.eulerCharacteristic_pos_of_field :
    ∀ {R : Type u} [CommRing R] [IsRegularLocalRing R]
      (M N : ModuleCat.{u} R)
      [Module.Finite R M] [Module.Finite R N]
      [Nontrivial M] [Nontrivial N]
      (_ : Module.support R (ModuleCat.TensorProduct.obj R M N) ⊆
        {IsLocalRing.closedPoint R})
      {k : Type u} [Field k] [Algebra k R]
      (_ : Module.supportDim R M + Module.supportDim R N = ringKrullDim R),
      0 < CategoryTheory.ModuleCat.Tor.eulerCharacteristic M N)
