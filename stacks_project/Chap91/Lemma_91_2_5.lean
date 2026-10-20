module

public import ReasLib.RingTheory.RingHom.SquareZero.Functoriality
import StacksCheckRecall

/-!
# Functoriality of square-zero A-algebra extensions

An A-algebra map B' → C' compatible with B → C and a coefficient map
c : M →ₗ[B] N exists if and only if the Ext¹ classes of the two extensions
agree in Ext¹_B(NL_{B/A}, N).
-/

@[expose] public section

noncomputable section

universe u

open RingHom.SquareZeroExtension

namespace RingHom.SquareZeroExtension

variable {A B C M N : Type u}
variable [CommRing A] [CommRing B] [CommRing C]
variable [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
variable [AddCommGroup M] [Module B M] [Module A M] [IsScalarTower A B M]
variable [AddCommGroup N] [Module C N] [Module B N] [Module A N]
variable [IsScalarTower B C N] [IsScalarTower A C N] [IsScalarTower A B N]

/- Lemma 91.2.5 Given ring maps A → B → C, a B-module M, a C-module N, a B-linear
map c : M →ₗ[B] N, and square-zero A-algebra extensions 0 → M → B' → B → 0 and
0 → N → C' → C → 0 classified by ξ = (algebraExtensionEquiv A B M).symm (isoClassMk SB)
and ζ = (algebraExtensionEquiv A C N).symm (isoClassMk SC), there is an A-algebra map
B' → C' compatible with B → C and c if and only if extOneNaiveCotangent_map c ξ
equals extOneNaiveCotangent_comap B ζ in Ext¹_B(NL_{B/A}, N). -/
@[stacks 0GPV]
#check (RingHom.SquareZeroExtension.fittingMap_nonempty_iff :
    ∀ (c : M →ₗ[B] N)
    (SB : @Solution A A _ _ B _ _ (RingHom.id A) _ M _ _ _ (zeroKernelMap A B M) _)
    (SC : @Solution A A _ _ C _ _ (RingHom.id A) _ N _ _ _ (zeroKernelMap A C N) _),
    Nonempty (FittingMap (RelativeDiagram.ofAlgebraMap c SB SC)) ↔
      extOneNaiveCotangent_map c ((algebraExtensionEquiv A B M).symm (isoClassMk SB)) =
        extOneNaiveCotangent_comap B
          ((algebraExtensionEquiv A C N).symm (isoClassMk SC)))

end SquareZeroExtension

end RingHom
