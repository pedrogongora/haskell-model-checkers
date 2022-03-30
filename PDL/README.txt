
Archivos:
    PDL.hs:     contiene el verificador
    NashEq.hs:  contiene ejemplos del método para calcular equilibrios

Para ejecutarlo necesitas el intérprede de Haskell. Puede ser hugs o ghci.
En el interprete puedes cargar cualquiera de los dos archivos NashEq.hs
carga el verificador y los ejemplos.

Por ejemplo, con hugs:

$ hugs
    Hugs> 
carga el intérprete.

    Hugs> :load NashEq.hs
    NashEq> 
carga el verficador y los ejemplos.

    NashEq> sort $ sat_in game1 $ bestSib 1 2
    ["z2","z4"]
    NashEq> 
calcula los nodos BS(1) (best sibling h=1) para el modelo game1.

En PDL.hs está el verificador. El algoritmo de etiquetamiento está implementado
en la función "sat_in", que recibe un modelo y una fórmula.
Hay varios modelos capturados en los dos archivos.
Las fórmulas se capturan como tipos de Haskell en notación prefija.

Por ejemplo, la fórmula:
    (p & q) -> r
se tiene que escribir:
    Imp (And (Prop "p") (Prop "q")) (Prop "r")

Las definiciones del tipo de datos para las fórmulas están al principio del
archivo PDL.hs
Hay un parser, pero está mal hecho, no te fijes mucho.

En NashEq.hs hay tres juegos. En comentarios hay ejemplos de cómo invocar
al verficador para calcular sus equilibrios.
Para el juego del ciempiés,  con altura h<3, el cálculo es inmediato.
Para altura h=3 tarda horas y, supongo, que para h>3 no termina en un tiempo
razonable.

