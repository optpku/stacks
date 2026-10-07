module

public import ReasLib.Algebra.Category.ModuleCat.ChangeOfRings.FaithfullyFlat
import StacksCheckRecall

@[expose] public section

open CategoryTheory Limits

universe v₁ v₂ u₁ u₂ u

/- Remark 35.4.4 (1): an exact functor between abelian categories which reflects zero
objects reflects monomorphisms. -/
@[stacks 08WK]
#check
  (@CategoryTheory.Functor.reflectsMonomorphisms_of_exact_of_kernel_le_isZero :
    ∀ {A : Type u₁} [Category.{v₁} A] [Abelian A]
      {B : Type u₂} [Category.{v₂} B] [Abelian B]
      (F : A ⥤ B), exactFunctor A B F → F.kernel ≤ IsZero →
        F.ReflectsMonomorphisms)

/- Remark 35.4.4 (2): an exact functor between abelian categories which reflects zero
objects reflects epimorphisms. -/
@[stacks 08WK]
#check
  (@CategoryTheory.Functor.reflectsEpimorphisms_of_exact_of_kernel_le_isZero :
    ∀ {A : Type u₁} [Category.{v₁} A] [Abelian A]
      {B : Type u₂} [Category.{v₂} B] [Abelian B]
      (F : A ⥤ B), exactFunctor A B F → F.kernel ≤ IsZero →
        F.ReflectsEpimorphisms)

/- Remark 35.4.4 (3): extension of scalars along a faithfully flat homomorphism of
commutative rings is exact. -/
@[stacks 08WK]
#check
  (@ModuleCat.ExtendScalars.exact_of_faithfullyFlat :
    ∀ {R S : Type u} [CommRing R] [CommRing S]
      (f : R →+* S), f.FaithfullyFlat →
        exactFunctor (ModuleCat.{u} R) (ModuleCat.{u} S)
          (ModuleCat.extendScalars.{u, u, u} f))

/- Remark 35.4.4 (4): extension of scalars along a faithfully flat homomorphism reflects
zero objects. -/
@[stacks 08WK]
#check
  (@ModuleCat.ExtendScalars.kernel_le_isZero_of_faithfullyFlat :
    ∀ {R S : Type u} [CommRing R] [CommRing S]
      (f : R →+* S), f.FaithfullyFlat →
        (ModuleCat.extendScalars.{u, u, u} f).kernel ≤ IsZero)

/- Remark 35.4.4 (5): extension of scalars along a faithfully flat homomorphism reflects
monomorphisms. -/
@[stacks 08WK]
#check
  (@ModuleCat.ExtendScalars.reflectsMonomorphisms_of_faithfullyFlat :
    ∀ {R S : Type u} [CommRing R] [CommRing S]
      (f : R →+* S), f.FaithfullyFlat →
        (ModuleCat.extendScalars.{u, u, u} f).ReflectsMonomorphisms)

/- Remark 35.4.4 (6): extension of scalars along a faithfully flat homomorphism reflects
epimorphisms. -/
@[stacks 08WK]
#check
  (@ModuleCat.ExtendScalars.reflectsEpimorphisms_of_faithfullyFlat :
    ∀ {R S : Type u} [CommRing R] [CommRing S]
      (f : R →+* S), f.FaithfullyFlat →
        (ModuleCat.extendScalars.{u, u, u} f).ReflectsEpimorphisms)
