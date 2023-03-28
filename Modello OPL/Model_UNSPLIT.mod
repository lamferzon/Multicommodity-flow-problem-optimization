/*********************************************
 * OPL 22.1.0.0 Model
 * Author: Lorenzo Leoni
 * Creation Date: 27 mag 2022 at 15:08:25
 *********************************************/
 
 // Multicommodity flow problem e network design problem con traffici UNSPLITTABLE
 
 // INSIEMI
 {string} CSs = ...; // insieme dei siti candidati CSs (Candidate Sites)
 {string} TPs = ...; // insieme dei nodi sorgente TPs (Test Points)
 {string} DNs = ...; // insieme dei nodi destinazione DNs (Destination Nodes)
 {string} INs = ...; // insieme dei canali di accesso alla rete INs (INputs)
 {string} OUTs = ...; // insieme dei canali di uscita dalla rete OUTs (OUTputs)
 {string} TRASFs = ...; // insieme dei canali di trasferimento all'interno della rete TRASFs (TRASFers)
 
 // STRUTTURE DATI
 // definizione della tupla contenente le specifiche del router che potrebbe essere installato presso uno specifico CS
 tuple datiNodo{ 
   float Capacita;
   float CostoInst;
 }
 
 // definizione della tupla contenente i dati del canale di trasmissione
 tuple datiCanale{ 
   string Sorgente;
   string Destinazione;
   float Capacita;
   float CostoAttrav;
 }
 
 // DATI
 datiNodo CS[CSs] = ...; // associazione a ogni CS delle specifiche del router che ivi potrebbe essere installato 
 datiCanale Input[INs] = ...; // associazione a ogni canale di accesso delle rispettive specifiche
 datiCanale Output[OUTs] = ...; // associazione a ogni canale di uscita delle rispettive specifiche
 datiCanale Trasferimento[TRASFs] = ...; // associazione a ogni canale di traferimento delle rispettive specifiche
 float Traffico[TPs][DNs] = ...; // traffico da un TP a uno specifico DN
 
 // VARIABILI DECISIONALI
 dvar boolean x[INs]; // variabile binaria che indica se un TP è assegnato o meno a uno specifico CS
 dvar boolean z[CSs]; // variabile binaria che indica se un router è installato o meno presso uno specifico CS
 dvar boolean w[OUTs]; // variabile binaria che indica se un CS è connesso o meno a uno specifico DN
 dvar boolean y[TRASFs][DNs]; /* variabile binaria che indica se un canale di trasferimento è assegnato o meno
 al traffico diretto verso uno specifico DN */
 dvar float+ f1[TRASFs][DNs]; // traffico instradato su un canale di trasferimento verso uno specifico DN
 dvar float+ f2[OUTs]; // traffico instradato da un CS a uno specifico DN
 
 // FUNZIONE OBIETTIVO
 minimize 
 	// costo totale di installazione dei router
 	sum(j in CSs) (CS[j].CostoInst*z[j]) + 
 	// costo totale dovuto al trasferimento dei traffici all'interno della rete di backbone
 	sum(a in TRASFs, k in DNs)(Trasferimento[a].CostoAttrav*f1[a][k]) + 
 	// costo totale dovuto all'accesso dei TP ai rispettivi access point (router installati presso i CS)
 	sum(a in INs, k in DNs) (Input[a].CostoAttrav*Traffico[Input[a].Sorgente][k]*x[a]) + 
 	// costo totale dovuto alla trasmissione dei traffici verso i rispettivi DN
 	sum(a in OUTs) (Output[a].CostoAttrav*f2[a]*w[a]);
 
 // VINCOLI
 subject to{
   // vincoli di univocità della connessione di accesso: l'i-esimo TP dev'essere collegato a uno e a un solo access point
   forall(i in TPs){
     vinAccessPointUnivoco:
     sum(a in INs: Input[a].Sorgente == i) x[a] == 1;
   }
   /* vincoli di coerenza relativi all'accesso alla rete: affinché un canale di accesso alla rete di backbone (i,j) venga 
   attivato è necessario che un access point venga installato presso il j-esimo CS */
   forall(a in INs){
   	 vinCoerAccesso:
     x[a] <= z[Input[a].Destinazione];
   }
   /* vincoli di coerenza relativi all'uscita dalla rete: affinché un canale di uscita dalla rete di backbone (j,k) venga
   attivato è necessario che un router venga installato presso il j-esimo CS */
   forall(a in OUTs){
     vinCoerUscita:
     w[a] <= z[Output[a].Sorgente];
   }
   // vincoli di conservazione del traffico ai nodi della backbone
   forall(k in DNs){
     forall(j in CSs){
       vinConsTraffico:
       sum(a in INs: Input[a].Destinazione == j) (Traffico[Input[a].Sorgente][k]*x[a]) + 
       sum(a in TRASFs: Trasferimento[a].Destinazione == j) (f1[a][k]) - 
       sum(a in TRASFs: Trasferimento[a].Sorgente == j) (f1[a][k]) 
       - sum(a in OUTs: Output[a].Sorgente == j && Output[a].Destinazione == k) (f2[a]) == 0;
     }
   }
   /* vincoli di capacità relativi ai canali di trasferimento: la somma dei traffici che percorrono il canale di 
   trasferimento (j,l) non deve eccedere la sua capacità. Tali vincoli vengono abilitati soltanto se sia presso i sia
   presso j è installato un router */
   forall(a in TRASFs){
     vinCapTrasf1:
     sum(k in DNs) f1[a][k] <= Trasferimento[a].Capacita*z[Trasferimento[a].Sorgente];
     vinCapTrasf2:
     sum(k in DNs) f1[a][k] <= Trasferimento[a].Capacita*z[Trasferimento[a].Destinazione];
   }
   /* vincoli di capacità relativi agli access point: la somma dei traffici entranti in il j-esimo access point non
   devono eccedere la sua capacità */
   forall(j in CSs){
     vinCapAccessPoint:
     sum(a in INs: Input[a].Destinazione == j, k in DNs) Traffico[Input[a].Sorgente][k]*x[a] <= CS[j].Capacita;
   }
   /* vincoli di capacità relativi ai canali di uscita: la somma dei traffici che percorrono il canale di uscita (j,k) non
   deve eccedere la sua capacità. Tali vincoli vengono abilitati soltanto il canale di uscita (j,k) è attivo*/
   forall(a in OUTs){
     vinCapUscita:
     f2[a] <= Output[a].Capacita*w[a];
   }
   /* vincoli di coerenza relativi alla non suddivisione dei traffici, ossia alle variabili binarie y */
   forall(a in TRASFs){
     forall(k in DNs){
       vinCoerUnsplit1:
       f1[a][k] <= Trasferimento[a].Capacita*y[a][k];
       y[a][k] <= f1[a][k];
     }
   }
   /* vincoli di non suddivisione dei traffici: un flusso diretto verso uno specifico DN dev'essere instradato 
   da ogni ruoter installato presso un determinato CS verso uno e un solo arco di trasferimento */
   forall(k in DNs){
     forall(j in CSs){
       vinUnsplit:
       sum(a in TRASFs: Trasferimento[a].Sorgente == j) y[a][k] <= 1;
     }
   }
 }