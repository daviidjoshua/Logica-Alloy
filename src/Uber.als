module src

// Criação de Usuários 

abstract sig User {
    region: one Region
}

one sig Estudante, Professor, Servidor extends User{}

sig Motorista in User {}
sig Passageiro in User {}

// Débitos e Créditos de motoristas e Passageiros

sig Debito in Passageiro {}
sig Credito in Motorista {}

// Criação das Regiões

abstract sig Region{}
one sig Centro, Oeste, Leste, Norte, Sul extends Region {}

// Criação dos Horários de Corridas

abstract sig Horario {}

one sig ida_8, ida_10, ida_14, ida_16 extends Horario {}
one sig saida_10, saida_12, saida_16, saida_18 extends Horario {}

// Criação da corrida

sig Uber {
    region: one Region,
    horarioSaida: one Horario,
    motorista: one Motorista,
    passageiros: set Passageiro
}


// Valida se o número de passageiros está dentro do limite e se o passageiro não é motorista
pred checkPassageiros[u:Uber] {
    #u.passageiros > 0
    #u.passageiros <= 3
    
    all p: u.passageiros |
        (p !in Motorista)
}

// Verifica se o motorista do uber não é passageiro
pred checkMotorista[u:Uber] {
    u.motorista !in u.passageiros
    u.motorista !in Passageiro
}

// A região do uber sempre será a mesma de quem for o motorista ou passageiro do uber
pred checkRegion[u: Uber] {
    u.motorista.region = u.region

    all p: u.passageiros |
        (p.region = u.region) and (p.region = u.motorista.region)
}

fact {
    all u:Uber | checkPassageiros[u] && 
        checkMotorista[u] && checkRegion[u]
}

// Garante que todos da mesma região vão ficar na mesma corrida
fact {
    all u : Uber | all us : User |
        (us in u.passageiros || us in u.motorista) iff (u.region = us.region)
}

// Para todos Ubers e Motoristas, todos os motoristas estarão no conjunto motorista do uber
fact { some u: Uber | all m: Motorista | m in u.motorista}

// Para Todos Ubers e Todos os Passageiros, todos os passageiros serão do conjunto passageiros do uber
fact { some u: Uber | all p: Passageiro | p in u.passageiros }


// Para todo passageiro existirá um débito nele
fact { all p:Passageiro | one d:Debito | d in p }

// Para todo motorista existirá um crédito nele
fact { all m:Motorista | one c:Credito | c in m }


run{}
