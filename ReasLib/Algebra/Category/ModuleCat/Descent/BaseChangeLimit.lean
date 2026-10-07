module

public import ReasLib.Algebra.Category.ModuleCat.Descent.UniversallyInjective
public import ReasLib.LinearAlgebra.UniversallyInjective.FaithfullyFlat

@[expose] public section

open CategoryTheory
open CategoryTheory.Limits

namespace ModuleCat.DescentPushforward

universe u

/-- If an algebra map has an explicit linear retraction, then scalar extension carries the
canonical descent-pushforward equalizer fork to a limiting fork. -/
theorem baseChangeIsLimit_of_retraction
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (r : S →ₗ[R] R) (h_r : r.comp (Algebra.linearMap R S) = LinearMap.id)
    (D : (ModuleCat.extendRestrictScalarsAdj.{u}
      (algebraMap R S)).toComonad.Coalgebra) :
    Nonempty (IsLimit (baseChangeFork (algebraMap R S) D)) := sorry

/-- If an algebra map is faithfully flat, then scalar extension carries the canonical
descent-pushforward equalizer fork to a limiting fork. -/
theorem baseChangeIsLimit_of_faithfullyFlat
    {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (h_f : (algebraMap R S).FaithfullyFlat)
    (D : (ModuleCat.extendRestrictScalarsAdj.{u}
      (algebraMap R S)).toComonad.Coalgebra) :
    Nonempty (IsLimit (baseChangeFork (algebraMap R S) D)) := sorry

end ModuleCat.DescentPushforward
