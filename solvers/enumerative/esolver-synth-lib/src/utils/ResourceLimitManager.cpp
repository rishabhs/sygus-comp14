// ResourceLimitManager.cpp --- 
// 
// Filename: ResourceLimitManager.cpp
// Author: Abhishek Udupa
// Created: Wed Jan 15 14:53:50 2014 (-0500)
// 
// 
// Copyright (c) 2013, Abhishek Udupa, University of Pennsylvania
// All rights reserved.
// 
// Redistribution and use in source and binary forms, with or without
// modification, are permitted provided that the following conditions are met:
// 1. Redistributions of source code must retain the above copyright
//    notice, this list of conditions and the following disclaimer.
// 2. Redistributions in binary form must reproduce the above copyright
//    notice, this list of conditions and the following disclaimer in the
//    documentation and/or other materials provided with the distribution.
// 3. All advertising materials mentioning features or use of this software
//    must display the following acknowledgement:
//    This product includes software developed by The University of Pennsylvania
// 4. Neither the name of the University of Pennsylvania nor the
//    names of its contributors may be used to endorse or promote products
//    derived from this software without specific prior written permission.
// 
// THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDER ''AS IS'' AND ANY
// EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
// WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
// DISCLAIMED. IN NO EVENT SHALL THE COPYRIGHT HOLDER BE LIABLE FOR ANY
// DIRECT, INDIRECT, INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES
// (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
// LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND
// ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
// (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF THIS
// SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
// 
// 

// Code:


#include "../utils/ResourceLimitManager.hpp"
#include <time.h>
#include <signal.h>
#include "../exceptions/ESException.hpp"
#include <sys/time.h>
#include <sys/resource.h>

// Z3 seems to use some RT signals. We play it safe and use the
// signal from the high end
#define TIMER_SIG_NUM (SIGRTMAX - 1)

namespace ESolver {

    uint64 ResourceLimitManager::MemLimit = MEM_LIMIT_INFINITE;
    uint64 ResourceLimitManager::CPULimit = CPU_LIMIT_INFINITE;
    bool ResourceLimitManager::TimerHandlerInstalled = false;
    bool ResourceLimitManager::TimerCreated = false;
    timer_t ResourceLimitManager::TimerID = (timer_t)0;
    struct sigaction ResourceLimitManager::OldAction;
    uint64 ResourceLimitManager::TimerFrequency = ESOLVER_TIMER_INTERVAL;

    bool ResourceLimitManager::TimeOut = false;
    bool ResourceLimitManager::MemOut = false;
    
    void ResourceLimitManager::TimerHandler(int SigNum, siginfo_t* SigInfo, void* Context)
    {
        // Check resource usage
        struct rusage CurUsage;
        getrusage(RUSAGE_SELF, &CurUsage);
        if ((uint64)CurUsage.ru_maxrss * 1024 >= MemLimit) {
            MemOut = true;
        }
        double UCPUTime = (double)((CurUsage.ru_utime.tv_sec * (uint64)1000000) + 
                                   CurUsage.ru_utime.tv_usec) / 1000000.0;
        double SCPUTime = (double)((CurUsage.ru_stime.tv_sec * (uint64)1000000) + 
                                   CurUsage.ru_stime.tv_usec) / 1000000.0;
        uint64 TotalTime = (uint64)(UCPUTime + SCPUTime);
        if (TotalTime >= CPULimit) {
            TimeOut = true;
        }
        
        // Call any other registered handlers
        if ((OldAction.sa_flags & SA_SIGINFO) != 0 && OldAction.sa_sigaction != nullptr) {
            OldAction.sa_sigaction(SigNum, SigInfo, Context);
        } else if(OldAction.sa_handler != nullptr) {
            OldAction.sa_handler(SigNum);
        }
    }

    void ResourceLimitManager::RegisterTimerHandler()
    {
        if (TimerHandlerInstalled) {
            return;
        }
        // Empty out the old action first
        OldAction.sa_handler = nullptr;
        OldAction.sa_sigaction = nullptr;
        sigemptyset(&OldAction.sa_mask);
        OldAction.sa_flags = 0;
        OldAction.sa_restorer = nullptr;

        struct sigaction NewAction;
        NewAction.sa_handler = nullptr;
        NewAction.sa_sigaction = ResourceLimitManager::TimerHandler;
        sigemptyset(&NewAction.sa_mask);
        NewAction.sa_flags = SA_SIGINFO;
        NewAction.sa_restorer = nullptr;

        // Register the new handler
        sigaction(TIMER_SIG_NUM, &NewAction, &OldAction);
        TimerHandlerInstalled = true;

        if (TimerCreated) {
            return;
        }
        struct sigevent SigEvent;
        SigEvent.sigev_notify = SIGEV_SIGNAL;
        SigEvent.sigev_signo = TIMER_SIG_NUM;
        SigEvent.sigev_value.sival_ptr = nullptr;
        timer_create(CLOCK_PROCESS_CPUTIME_ID, &SigEvent, &TimerID);
        TimerCreated = true;
    }

    void ResourceLimitManager::UnregisterTimerHandler()
    {
        if (!TimerHandlerInstalled) {
            return;
        }
        
        if (TimerCreated) {
            timer_delete(TimerID);
            TimerCreated = false;
        }

        // restore the old action
        if (OldAction.sa_handler != nullptr || OldAction.sa_sigaction != nullptr) {
            sigaction(TIMER_SIG_NUM, &OldAction, NULL);
        }
        TimerHandlerInstalled = false;
    }

    ResourceLimitManager::ResourceLimitManager()
    {
        // Nothing here
    }

    ResourceLimitManager::ResourceLimitManager(const ResourceLimitManager& Other)
    {
        // Nothing here
    }

    void ResourceLimitManager::SetMemLimit(uint64 MemLimit)
    {
        ResourceLimitManager::MemLimit = MemLimit;
    }

    uint64 ResourceLimitManager::GetMemLimit()
    {
        return ResourceLimitManager::MemLimit;
    }

    void ResourceLimitManager::SetCPULimit(uint64 CPULimit)
    {
        ResourceLimitManager::CPULimit = CPULimit;
    }

    void ResourceLimitManager::SetTimerFrequency(uint64 TimerFreqNS)
    {
        TimerFrequency = TimerFreqNS;
    }

    void ResourceLimitManager::QueryStart()
    {
        // install handlers IF resource limits are specified
        if (MemLimit != MEM_LIMIT_INFINITE ||
            CPULimit != CPU_LIMIT_INFINITE) {
            
            RegisterTimerHandler();
            struct itimerspec FreqSpec;
            FreqSpec.it_value.tv_sec = 0;
            FreqSpec.it_value.tv_nsec = TimerFrequency;
            FreqSpec.it_interval.tv_sec = 0;
            FreqSpec.it_interval.tv_nsec = TimerFrequency;
            timer_settime(TimerID, 0, &FreqSpec, NULL);
        }
        TimeOut = MemOut = false;
    }

    void ResourceLimitManager::QueryEnd()
    {
        if (TimerCreated) {
            // Just reset the timer
            struct itimerspec FreqSpec;
            FreqSpec.it_interval.tv_sec = 0;
            FreqSpec.it_interval.tv_nsec = 0;
            FreqSpec.it_value.tv_sec = 0;
            FreqSpec.it_value.tv_nsec = 0;
            timer_settime(TimerID, 0, &FreqSpec, NULL);
        }
        TimeOut = MemOut = false;
    }

    bool ResourceLimitManager::CheckTimeOut()
    {
        return (volatile bool)TimeOut;
    }

    bool ResourceLimitManager::CheckMemOut()
    {
        return (volatile bool)MemOut;
    }

    void ResourceLimitManager::GetUsage(double& TotalTime, double& PeakMem)
    {
        struct rusage CurUsage;
        getrusage(RUSAGE_SELF, &CurUsage);
        double UCPUTime = (double)((CurUsage.ru_utime.tv_sec * (uint64)1000000) + 
                                   CurUsage.ru_utime.tv_usec) / 1000000.0;
        double SCPUTime = (double)((CurUsage.ru_stime.tv_sec * (uint64)1000000) + 
                                   CurUsage.ru_stime.tv_usec) / 1000000.0;
        TotalTime = (UCPUTime + SCPUTime);
        PeakMem = (double)CurUsage.ru_maxrss / 1024.0;
    }

} /* End namespace */


// 
// ResourceLimitManager.cpp ends here
