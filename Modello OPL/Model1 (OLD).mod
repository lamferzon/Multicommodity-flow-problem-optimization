/*********************************************
 * OPL 22.1.0.0 Model
 * Author: Lorenzo Leoni
 * Creation Date: 27 mag 2022 at 15:08:25
 *********************************************/

 {string} Nodi = ...; // insieme dei nodi
 {string} Archi = ...; // insieme degli archi
 {string} Domande = ...; // insieme delle domande
 
 tuple datiArco{ // definizione della tupla contenente i dati dell'arco
   string NodoSorg;
   string NodoDest;
   float Capacita;
   float Costo;
 }
 
 tuple datiDomanda{ // definizione della tupla contenente i dati della domanda
   string NodoSorg;
   string NodoDest;
   float FlussoRichiesto;
 }
 
 datiArco Arco[Archi] = ...; // associazione a ogni arco delle rispettive informazioni
 datiDomanda Domanda[Domande] = ...; // associazione a ogni domanda delle rispettive informazioni
 
 dvar float+ x[Archi][Domande]; // flusso sull'a-esimo arco riferito alla k-esima domanda
 dvar boolean y[Archi][Domande]; // associazione all'a-esimo arco della k-esima domanda
 
 minimize sum(a in Archi, k in Domande) Arco[a].Costo*x[a][k]*y[a][k];
 
 subject to{
   // vincoli di capacità
   forall(a in Archi){
     sum(k in Domande) x[a][k] <= Arco[a].Capacita;
   }
   // vincoli di conservazione del flusso ai nodi
   forall(k in Domande){
     forall(i in Nodi){
       // se l'i-esimo nodo della k-esima domanda è di input, allora:
       if(i == Domanda[k].NodoSorg){
         sum(a in Archi: Arco[a].NodoSorg == i) (x[a][k]) - 
         sum(a in Archi: Arco[a].NodoDest == i) (x[a][k]) == Domanda[k].FlussoRichiesto;
       }
       // se l'i-esimo nodo della k-esima domanda è di output, allora:
       if(i == Domanda[k].NodoDest){
         sum(a in Archi: Arco[a].NodoSorg == i) (x[a][k]) - 
         sum(a in Archi: Arco[a].NodoDest == i) (x[a][k]) == -Domanda[k].FlussoRichiesto;
       }
       // se l'i-esimo nodo della k-esima domanda è di trasferimento, allora
       if(i != Domanda[k].NodoSorg && i != Domanda[k].NodoDest){
         sum(a in Archi: Arco[a].NodoSorg == i) (x[a][k]) - 
         sum(a in Archi: Arco[a].NodoDest == i) (x[a][k]) == 0;
       }
     }
   }
   // vincoli di coerenza
   forall(a in Archi){
     forall(k in Domande){
       x[a][k] <= Arco[a].Capacita*y[a][k];
     }
   }
   // vincoli per la non suddivisione del flusso ai nodi relativo a una specifica domanda
   forall(k in Domande){
     forall(i in Nodi){
       if (i != Domanda[k].NodoDest){
         sum(a in Archi: Arco[a].NodoSorg == i) (y[a][k]) <= 1;
       }
     }
   }
 }