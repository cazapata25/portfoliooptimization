
## ---------------------------------------------------------------------------
## Teoria de portafolios - 2021-2
## Funciones optimizacion de portafolios: Markowitz, Sharpe, Sortino, Treynor
## Omega, CVaR y evaluación de desempeño
## Universidad Externado de Colombia
## Prof. Carlos Zapata
## @CpR- 2021 
## ---------------------------------------------------------------------------

## ---------------------------------------------------------------------------
## Importar precios Yahoo Finance

f.precios <- function(activos,fechai,fechaf,periodicidad){
    precios <- xts()
    for(i in 1:length(activos)){
        aux <- Ad(getSymbols(activos[i],from=fechai,to=fechaf,
                             periodicity=periodicidad,auto.assign=FALSE))
        aux <- na.approx(aux,na.rm=FALSE) # Interpolación de datos con NA
        precios <- cbind(precios,aux)
    }
    colnames(precios) <- activos
    tclass(precios) <- "Date"
    print("Los precios han sido importados correctamente")
    return(precios)
}

## ---------------------------------------------------------------------------
## Modelo MV: Markowitz y Sharpe
## Con cortos (permite pesos negativos): 1
## Sin cortos (no pesos negativos): 0
##-------------------------------------------

modeloMV <- function(ret){
    # Inputs
    rf <- rf
    mu <- colMeans(ret)
    cov <- cov(ret)
    activos <- names(ret)

    # Optimizacion sin restricciones en cortos
    if(short == 1){
        ones <- rep(1,n)
        x <- t(mu)%*%solve(cov)%*%mu
        y <- t(mu)%*%solve(cov)%*%ones
        z <- t(ones)%*%solve(cov)%*%ones
        d <- x*z - y*y
        g <- (solve(cov,ones)%*%x-solve(cov,mu)%*%y)%*%solve(d)
        h <- (solve(cov,mu)%*%z-solve(cov,ones)%*%y)%*%solve(d)
        rpmin <- min(mu)
        rpmax <- max(mu)*1.5
        nport <- 1000
        j <- seq(rpmin,rpmax, length=nport) 
        wpo <- matrix(c(0), ncol=n, nrow=nport) 
        rpo <- matrix(c(0), nrow=nport)
        sigmapo <- matrix(c(0), nrow=nport)
        wj <- 0
        cont <- 1
        for(i in 1:nport){
            wj <- g + h*j[i] 
            wpo[cont,] <- t(wj)
            rpo[cont,] <- t(wj)%*%mu
            sigmapo[cont,] <- sqrt(t(wj)%*%cov%*%wj)
            cont <- cont+1
        }
        # PMVG
        cov_inv_1 <- solve(cov, ones) 
        wpmvg <- (1/as.numeric(ones %*% cov_inv_1)) * cov_inv_1
        rpmvg <- mu%*%wpmvg
        sigmapmvg <- sqrt(t(wpmvg)%*%cov%*%wpmvg)
        # Sharpe
        Er <- mu-rf 
        Z <- solve(cov,Er)  
        sumZ <- sum(Z) 
        wpt <- Z/sumZ 
        rpt <- t(wpt)%*%mu
        sigmapt <- sqrt(t(wpt)%*%cov%*%wpt)
        wpmvg <- t(wpmvg)
        wpt <- t(wpt)
        
        MV <- list()
        MV[[1]] <- wpo
        MV[[2]] <- rpo
        MV[[3]] <- sigmapo
        MV[[4]] <- t(wpmvg)
        MV[[5]] <- rpmvg
        MV[[6]] <- sigmapmvg
        MV[[7]] <- t(wpt)
        MV[[8]] <- rpt 
        MV[[9]] <- sigmapt
        return(MV)
    }
    # Con restricciones en corto
    else {
    # FE    
    library(quadprog)
    if(min(mu) > 0){rpmin = min(mu)*1.001}
    else{rpmin = 0.00}
    rpmax <- max(mu)*0.999
    n <- length(mu)
    nport <- 1000
    j <- seq(rpmin,rpmax,length=nport)
    sigmapo <- matrix(0,nrow=nport)
    wpo <- matrix(0,nrow=nport, ncol=n)
    Amat <- t(rbind(rep(1,n),mu,diag(1,nrow=n)))
    dvec <- rep(0,n) 
    Dmat <- 2*cov
    for(i in 1:nport){
      bvec <- c(1,j[i],rep(0,n))
      result <- solve.QP(Dmat=Dmat,dvec=dvec,Amat=Amat,bvec=bvec,meq=2)
      wpo[i,] <- result$solution
      sigmapo[i,] <- sqrt(result$value)
    }
    rpo <- j
    colnames(wpo) <- c(activos)
    # PMVG
    pmvg <- cbind(sigmapo,wpo)
    pmvg.sort <- pmvg[order(pmvg[,1]),]
    pmvg.sel <- cbind(pmvg.sort[1,])
    wpmvg <- cbind(round(pmvg.sel[2:length(pmvg.sel)],6))
    rownames(wpmvg) <- c(activos)
    rpmvg <- mu%*%wpmvg
    sigmapmvg <- sqrt(t(wpmvg)%*%cov%*%wpmvg)
    # Sharpe    
    sharpe_port <- (rpo-rf)/sigmapo
    sharpe <- cbind(sharpe_port,wpo)
    sharpe.sort <- sharpe[order(-sharpe[,1]),]
    sharpe.sel <- cbind(sharpe.sort[1,])
    wpt <- round(cbind(sharpe.sel[2:length(sharpe.sel)]),6)
    rownames(wpt) <- c(activos)
    rpt <- mu%*%wpt
    sigmapt <- sqrt(t(wpt)%*%cov%*%wpt)

    MV <- list()
    MV[[1]] <- wpo
    MV[[2]] <- rpo
    MV[[3]] <- sigmapo
    MV[[4]] <- wpmvg
    MV[[5]] <- rpmvg
    MV[[6]] <- sigmapmvg
    MV[[7]] <- wpt
    MV[[8]] <- rpt 
    MV[[9]] <- sigmapt
    return(MV)
    }
}

## ---------------------------------------------------------------------------
## Modelo de Sortino

m.sortino <- function(retornos,h){
    # Inputs
    rf <- rf
    mu <- colMeans(retornos)
    semiret <- pmin(retornos,h)
    semicov <- cov(semiret) # semi-covarianzas
    #cov <- semicov
    activos <- names(retornos)
    
    # Optimizacion sin restricciones en cortos
    if(short == 1){
        ones <- rep(1,n)
        x <- t(mu)%*%solve(semicov)%*%mu
        y <- t(mu)%*%solve(semicov)%*%ones
        z <- t(ones)%*%solve(semicov)%*%ones
        d <- x*z - y*y
        g <- (solve(cov,ones)%*%x-solve(semicov,mu)%*%y)%*%solve(d)
        h <- (solve(cov,mu)%*%z-solve(semicov,ones)%*%y)%*%solve(d)
        rpmin <- min(mu)
        rpmax <- max(mu)*1.5
        nport <- 1000
        j <- seq(rpmin,rpmax, length=nport) 
        wpo <- matrix(c(0), ncol=n, nrow=nport) 
        rpo <- matrix(c(0), nrow=nport)
        sigmapo <- matrix(c(0), nrow=nport)
        wj <- 0
        cont <- 1
        for(i in 1:nport){
            wj <- g + h*j[i] 
            wpo[cont,] <- t(wj)
            rpo[cont,] <- t(wj)%*%mu
            sigmapo[cont,] <- sqrt(t(wj)%*%semicov%*%wj)
            cont <- cont+1
        }
        # Tangente-Sortino
        Er <- mu-rf 
        Z <- solve(semicov,Er)  
        sumZ <- sum(Z) 
        wpt <- Z/sumZ 
        rpt <- t(wpt)%*%mu
        sigmapt <- sqrt(t(wpt)%*%semicov%*%wpt)
        wpmvg <- t(wpmvg)
        wpt <- t(wpt)
        
        SMV <- list()
        SMV[[1]] <- wpo
        SMV[[2]] <- rpo
        SMV[[3]] <- sigmapo
        SMV[[4]] <- t(wpt)
        SMV[[5]] <- rpt 
        SMV[[6]] <- sigmapt
        return(SMV)
    }
    # Con restricciones en corto
    else {
        # FE    
        library(quadprog)
        if(min(mu) > 0){rpmin = min(mu)*1.001}
        else{rpmin = 0.00}
        rpmax <- max(mu)*0.999
        n <- length(mu)
        nport <- 1000
        j <- seq(rpmin,rpmax,length=nport)
        sigmapo <- matrix(0,nrow=nport)
        wpo <- matrix(0,nrow=nport, ncol=n)
        Amat <- t(rbind(rep(1,n),mu,diag(1,nrow=n)))
        dvec <- rep(0,n) 
        Dmat <- 2*semicov
        for(i in 1:nport){
            bvec <- c(1,j[i],rep(0,n))
            result <- solve.QP(Dmat=Dmat,dvec=dvec,Amat=Amat,bvec=bvec,meq=2)
            wpo[i,] <- result$solution
            sigmapo[i,] <- sqrt(result$value)
        }
        rpo <- j
        colnames(wpo) <- c(activos)
        # Tangente-Sortino    
        sharpe_port <- (rpo-rf)/sigmapo
        sharpe <- cbind(sharpe_port,wpo)
        sharpe.sort <- sharpe[order(-sharpe[,1]),]
        sharpe.sel <- cbind(sharpe.sort[1,])
        wpt <- round(cbind(sharpe.sel[2:length(sharpe.sel)]),6)
        rownames(wpt) <- c(activos)
        rpt <- mu%*%wpt
        sigmapt <- sqrt(t(wpt)%*%semicov%*%wpt)
        
        SMV <- list()
        SMV[[1]] <- wpo
        SMV[[2]] <- rpo
        SMV[[3]] <- sigmapo
        SMV[[4]] <- wpt
        SMV[[5]] <- rpt 
        SMV[[6]] <- sigmapt
        return(SMV)
    }
}

## ---------------------------------------------------------------------------
## Modelo de Treynor

m.treynor <- function(retornos,r.indice){
    n <- ncol(retornos)
    betas <- matrix(0,ncol=n)
    varerror<- matrix(0,ncol=n)
    
    # Regresion iterativa para los parametros
    for(i in 1:n){
        modelo <- lm(retornos[,i]~r.indice)
        betas[i] <- modelo[["coefficients"]][2]
        varerror[i] <- var(modelo[["residuals"]])
    }
    
    treynori <- (mu-rf)/betas
    
    # Calculo de los ratios 1 y 2 y las sumas acumuladas
    matriz <- t(rbind(treynori,betas,varerror,mu,sigma))
    colnames(matriz) <- c("Treynor","Betas","VaError","Mu","Sigma")
    matriz.ord <- matriz[order(-matriz[,1]),]
    
    ratio1 <- ((matriz.ord[,4]-rf)*matriz.ord[,2])/matriz.ord[,3]
    ratio2 <- matriz.ord[,2]^2/matriz.ord[,3]
    suma1 <- cumsum(ratio1)
    suma2 <- cumsum(ratio2)
    sigmam <- sd(r.indice)
    tasac <- (sigmam^2*suma1)/(1+sigmam^2*suma2)
    
    diff <- matriz.ord[,1] - tasac
    cond.diff <- diff[!is.na(diff) & diff>0 ]
    n.optimo <- length(cond.diff)
    cmax <- tasac[n.optimo]
    
    zi <- (matriz.ord[,2]/matriz.ord[,3])*(matriz.ord[,1]-cmax)
    zi <- pmax(zi,0)
    
    wpot <- zi/sum(zi)
    wpot <- rbind(wpot[activos])
    wpot <- t(wpot)
    rpot <- t(wpot)%*%mu
    sigmapot <- sqrt(t(wpot)%*%cov%*%wpot)
    
    MT <- list()
    MT[[1]] <- wpot
    MT[[2]] <- rpot
    MT[[3]] <- sigmapot
    MT[[4]] <- n.optimo
    return(MT)
}

## ---------------------------------------------------------------------------
## Modelo Omega

f.omega <- function(retornos,h){
    library("ROI")
    library("ROML")
    library("ROML.portfolio")
    short <- short
    if(short == 1){lb=-1}
    else{lb=0}
    m <- model()
    m$variable(portfolio, lb = lb) # the portfolio choice vector; 
    m$maximize( omega(portfolio) )
    opt <- optimize(m, solver="glpk", 
                    data=list(returns = coredata(retornos))) 
    wpomega <- round(opt$solution[grep("portfolio", names(opt$solution))]/
                         opt$solution[grep("z", names(opt$solution))], 6)
    
    names(wpomega) <- activos
    rpomega <- mu%*%wpomega
    sigmapomega <- sqrt(t(wpomega)%*%cov%*%wpomega)
    
    PO <- list()
    PO[[1]] <- cbind(wpomega)
    PO[[2]] <- rpomega
    PO[[3]] <- sigmapomega
    return(PO)
}

## ---------------------------------------------------------------------------
## Modelo CVaR

f.cvar <- function(retornos,alpha){
    library("ROI")
    library("ROML")
    library("ROML.portfolio")
    alpha <- alpha
    short <- short
    if(short == 1){lb=-1}
    else{lb=0}
    m <- model()
    m$variable(portfolio, lb = lb) # the portfolio choice vector; 
    m$minimize( cvar(portfolio, alpha) )
    m$subject_to( budget_norm(portfolio) )
    opt <- optimize(m, solver="glpk", 
                    data=list(returns = coredata(retornos)))
    
    wpcvar <- round(opt$solution[grep("portfolio", names(opt$solution))], 4)
    names(wpcvar) <- activos
    
    rpcvar <- mu%*%wpcvar
    sigmapcvar <- sqrt(t(wpcvar)%*%cov%*%wpcvar)
    
    PCV <- list()
    PCV[[1]] <- cbind(wpcvar)
    PCV[[2]] <- rpcvar
    PCV[[3]] <- sigmapcvar
    return(PCV)
}


## ---------------------------------------------------------------------------
## Evaluacion de desempeño
## ---------------------------------------------------------------------------

performance <- function(retornos,r.indice){
  ret <- retornos
  t <- nrow(ret)
  n <- ncol(ret)
  activos <- colnames(ret)
  rport <- matrix(0,nrow=t,ncol=7)
  colnames(rport) <- c("PMVG","Sharpe","Benchmark","Treynor","Sortino","Omega","CVaR")
  vport <- matrix(0,nrow=t,ncol=7)
  colnames(vport) <- c("PMVG","Sharpe","Benchmark","Treynor","Sortino","Omega","CVaR")
    
  # Retornos
  # PMV
  rpmv <- ret%*%wpmv
  rport[,1] <- rpmv
  
  #Sharpe
  rpsharpe <- ret%*%wpt
  rport[,2] <- rpsharpe 
  
  # Benchmark
  r.benchmark <- r.indice
  rport[,3] <- r.benchmark
  
  # Treynor
  rptreynor <- ret%*%wpot
  rport[,4] <- rptreynor
  
  # Sortino
  rpsortino <- ret%*%wpts
  rport[,5] <- rpsortino
  
  # Omega
  rpomega <- ret%*%wpomega
  rport[,6] <- rpomega
  
  # CVaR
  rpcvar <- ret%*%wpcvar
  rport[,7] <- rpcvar
  
  # Valor del portafolio
  # PMV
  port.mv <- matrix(0, nrow=t)
  port.mv[1] <- valor
  for(i in 2:t){
    port.mv[i] <- port.mv[i-1]*exp(rpmv[i-1])
  }
  vport[,1] <- port.mv
  
  # Sharpe
  port.sharpe <- matrix(0, nrow=t)
  port.sharpe[1] <- valor
  for(i in 2:t){
  port.sharpe[i] <- port.sharpe[i-1]*exp(rpsharpe[i-1])
  }
  vport[,2] <- port.sharpe
  
  # Benchmark
  v.benchmark <- matrix(0, nrow=t)
  v.benchmark[1] <- valor
  
  for(i in 2:t){
    v.benchmark[i] <- v.benchmark[i-1]*exp(r.benchmark[i-1])
  }
  vport[,3] <- v.benchmark
  
  # Treynor
  v.treynor<- matrix(0, nrow=t)
  v.treynor[1] <- valor
  
  for(i in 2:t){
    v.treynor[i] <- v.treynor[i-1]*exp(rptreynor[i-1])
  }
  vport[,4] <- v.treynor
  
  # Sortino
  v.sortino <- matrix(0, nrow=t)
  v.sortino[1] <- valor
  
  for(i in 2:t){
    v.sortino[i] <- v.sortino[i-1]*exp(rpsortino[i-1])
  }
  vport[,5] <- v.sortino
  
  # Omega
  v.omega <- matrix(0, nrow=t)
  v.omega[1] <- valor
  
  for(i in 2:t){
    v.omega[i] <- v.omega[i-1]*exp(rpomega[i-1])
  }
  vport[,6] <- v.omega
  
  # CVaR
  v.cvar <- matrix(0, nrow=t)
  v.cvar[1] <- valor
  
  for(i in 2:t){
    v.cvar[i] <- v.cvar[i-1]*exp(rpcvar[i-1])
  }
  vport[,7] <- v.cvar
  
  DH <- list()
  DH[[1]] <- vport
  DH[[2]] <- rport
  return(DH)
}




