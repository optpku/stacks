module

public import ReasLib.RingTheory.Kaehler.DeRham.Connection

@[expose] public section

universe u v

/- The reusable exterior-calculus and connection API is owned by ReasLib. -/
#check ExteriorCalculus
#check ExteriorCalculus.of
#check Connection
#check Connection.differential
#check Connection.deRhamComplex
#check KaehlerDifferential.DeRham.descendedFamily
#check KaehlerDifferential.DeRham.integrableConnection_squaresToZero

end
