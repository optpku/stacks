module

public import Mathlib.Tactic.CrossRefAttribute
public import ReasLib.RingTheory.Henselian.Finite
public import ReasLib.RingTheory.QuasiFinite.FiniteType
public import ReasLib.RingTheory.QuasiFinite.Localization

@[expose] public section

/-!
# Quasi-finite local algebras over henselian bases

This leaf records the primewise finite and henselian consequences of a
finite-type quasi-finite algebra over a henselian local ring.  The statements
are independent of the construction of a henselization and therefore belong
to the reusable local-algebra layer.
-/

universe u v

open IsLocalRing

namespace HenselianLocalRing

namespace QuasiFiniteAt

variable {R : Type u} {S : Type v}
variable [hCommR : CommRing R] [hCommS : CommRing S] [hRS : Algebra R S]
variable [hR : HenselianLocalRing R]

include hCommR hCommS hRS hR

/-- Tag 04GH: a finite-type quasi-finite point above the closed point of a
henselian local base has henselian local prime localization. -/
@[stacks 04GH "henselian quasi-finite localization"]
theorem localizationAtPrime_henselian
    (q : Ideal S) [q.IsPrime]
    (hq : Ideal.comap (algebraMap R S) q = maximalIdeal R)
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    HenselianLocalRing (Localization.AtPrime q) := sorry

/-- Tag 04GH: a finite-type quasi-finite point above the closed point of a
henselian local base is module-finite after localization. -/
@[stacks 04GH "finite quasi-finite localization"]
theorem localizationAtPrime_moduleFinite
    (q : Ideal S) [q.IsPrime]
    (hq : Ideal.comap (algebraMap R S) q = maximalIdeal R)
    (hqf : Algebra.FiniteType.QuasiFiniteAt R S q) :
    Module.Finite R (Localization.AtPrime q) := sorry

end QuasiFiniteAt

namespace QuasiFinite

variable {R : Type u} {S : Type v}
variable [hCommR : CommRing R] [hCommS : CommRing S] [hRS : Algebra R S]
variable [hR : HenselianLocalRing R]

include hCommR hCommS hRS hR

/-- Tag 04GH: a point above the closed point of a finite-type quasi-finite
algebra over a henselian local ring has henselian local prime localization. -/
@[stacks 04GH "henselian quasi-finite localization"]
theorem localizationAtPrime_henselian
    (q : Ideal S) [q.IsPrime]
    (hq : Ideal.comap (algebraMap R S) q = maximalIdeal R)
    (hS : Algebra.FiniteType.QuasiFinite R S) :
    HenselianLocalRing (Localization.AtPrime q) := sorry

/-- Tag 04GH: a point above the closed point of a finite-type quasi-finite
algebra over a henselian local ring is module-finite after localization. -/
@[stacks 04GH "finite quasi-finite localization"]
theorem localizationAtPrime_moduleFinite
    (q : Ideal S) [q.IsPrime]
    (hq : Ideal.comap (algebraMap R S) q = maximalIdeal R)
    (hS : Algebra.FiniteType.QuasiFinite R S) :
    Module.Finite R (Localization.AtPrime q) := sorry

end QuasiFinite

end HenselianLocalRing
