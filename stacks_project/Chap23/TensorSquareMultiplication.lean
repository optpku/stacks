module

public import ReasLib.RingTheory.Algebra.TensorProduct.Multiplication.Perfect
public import ReasLib.RingTheory.RingHom.TorDimension
import StacksCheckRecall

@[expose] public section

open scoped TensorProduct

universe u v

variable (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]

/- Lemma 23.10.1 (Tag 0FCW) uses the canonical multiplication map from the tensor square. -/
@[stacks 0FCW "tensor-square multiplication"]
#check (Algebra.tensorSquareMultiplication A B : B ⊗[A] B →+* B)

#check @Algebra.tensorSquareMultiplication.apply_tmul

/- Lemma 23.10.2 (Tag 0FCX) uses the same canonical multiplication map. -/
@[stacks 0FCX "tensor-square multiplication"]
#check (Algebra.tensorSquareMultiplication A B : B ⊗[A] B →+* B)

#check @Algebra.tensorSquareMultiplication.smul_tmul
#check @RingHom.DiagonalIsPerfect
#check @RingHom.DiagonalHasFiniteTorDimension
#check @RingHom.diagonalIsPerfect_algebraMap
#check @RingHom.diagonalHasFiniteTorDimension_algebraMap
#check @RingHom.HasTorDimensionLE
#check @RingHom.HasFiniteTorDimension
#check @RingHom.HasFiniteTorDimension.exists_bound
#check @RingHom.HasTorDimensionLE.id
#check @RingHom.HasTorDimensionLE.comp
#check @RingHom.HasFiniteTorDimension.comp
