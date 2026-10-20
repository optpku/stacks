module

public import ReasLib.AlgebraicGeometry.Scheme.Module.Flat.Locus.WeaklyAssociated.FiniteType
import StacksCheckRecall

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Scheme.Modules

/- Lemma 38.13.11 (Finite type version of Theorem 38.13.6 (1): if `f : X ⟶ S` is locally
of finite type, `F` is a quasicoherent finite-type module on `X`, and `S.weakAss` is locally
finite, then the locus where `F` is flat over `S` is open. -/
@[stacks 05IQ]
#check (AlgebraicGeometry.Scheme.Modules.IsFiniteType.isOpen_flatOverAt_of_locallyFinite_weakAss :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
    IsOpen {x : X | flatOverAt F f x})

/- Lemma 38.13.11 (Finite type version of Theorem 38.13.6 (2): on the relative-flatness
locus, the restriction of `F` is flat over `S`. -/
@[stacks 05IQ]
#check (AlgebraicGeometry.Scheme.Modules.IsFiniteType.flatOverLocus_isFlatOver :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
    flatOver
      (F.restrict (IsFiniteType.flatOverLocus f F h_weakAss).ι)
      ((IsFiniteType.flatOverLocus f F h_weakAss).ι ≫ f))

/- Lemma 38.13.11 (Finite type version of Theorem 38.13.6 (3): on the relative-flatness
locus, the restriction of `F` is finitely presented relative to `S`. -/
@[stacks 05IQ]
#check (AlgebraicGeometry.Scheme.Modules.IsFiniteType.flatOverLocus_isFinitePresentationOver :
  ∀ {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (h_weakAss : LocallyFinite (fun s : S.weakAss ↦ ({s.1} : Set S))),
    (F.restrict (IsFiniteType.flatOverLocus f F h_weakAss).ι).IsFinitePresentationOver
      ((IsFiniteType.flatOverLocus f F h_weakAss).ι ≫ f))

end AlgebraicGeometry.Scheme.Modules
